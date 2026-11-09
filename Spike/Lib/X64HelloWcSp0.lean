/-
**hello.w's `wc_main` from the box's allocator's return to `.x23`** (x86-64; the twin of
`Spike/Lib/A64HelloWcSp0.lean`), inside `W`, in any valid layout of `helloCells`, from checks decided once on the
cells (`decide +kernel`). It is `X64WakeWcSp0` and `X64WakeWcRes` at hello's `wc_main` (frame 128, the cell at
`-48(%rbp)`):

    .Lwc_main.x0:                      -- %rax = the box's cell (Alloc.EB)
      movq %rax, -48(%rbp); movq -48(%rbp), %rcx; movq $0, %rax  (wcS0H)
      movq %rax, (%rcx)                 -- row: the box's store (Out.newStore)
      # fence st: no code under TSO
      call scc_rt_thread_reserve        -- `.x22 + 18` (resBH), `.x23` pushed
    .Lwc_main.x1:                      -- %rax = n + 1 = 1

There are two segments, as in wake. The first ends at the box's store: for every fresh label `l` the pair lands at
`bXH l A` (on `R.fp (-8)`), which one `ms.xa` continues in (`hxa`, the instance's choice). The second starts from
that landing and runs the reserve at the counter's old value `0`.

**The region's re-basing.** Up to the store the nodes are on `wc_main`'s region `R` as handed over at the call
(based at the return address's cell, `X64HelloWcPre`: offsets `oWRH = ⟨-136, [(.rbp, -8)]⟩`, the cell at slot
`-56`). The landing `bXH` is stated on `R.fp (-8)`, the frame based at the saved `%rbp`, at
`X64HelloWcSp6.oWH = ⟨-128, [(.rbp, 0)]⟩` (the cell at `-48`, the spills at `-8 .. -40`, the caller's `%rbp` and
return address at `0` and `8`), the region and offsets every later `wc_main` piece is stated on. The store's
landing `bXRH` on `R` is carried there by `At.rebase` (`bXRH_rebase`): this is the only re-basing.

- `wcS0H`, `wcS0InH`, `hello_wcS0InH`, `resBH`, `wcResInH`, `hello_wcResInH`, `hello_reserveIn`: the blocks, rows
  and checks.
- `sNH`, `wcJFH`, `bXRH`, `bXH`, `so_rebase_wcMainH`, `bXRH_rebase`, `WcSp0WH`, `hello_wc_sp0_segW`: `.x22` to the
  box's store's landing.
- `bXH_slots`, `rJH`, `rNH`, `rXH`, `rARH`, `ResCtxH`, `WcResWH`, `hello_wc_res_segW`: the landing to `.x23`.

## Differences from the AArch64 version

- No fence node: hello's x86-64 listing has no instruction for the box's `publish` here (`# fence st` emits no
  code under TSO), so the reserve's segment takes no source step and has no `S`/`hfr` (AArch64: the `dmb ishst`
  node `.f`, `FenceRun.pub` to `S l A`). The source's publication and its run to the spawn
  (`X64HelloMainPreSrc.src_spawnH`) are taken at `wc_main`'s `mfence` (`.x25 + 44`, `X64HelloWcSp6.wcN6fH`), as
  in x86-64 wake (`X64WakeWcRes`'s docstring). `WcResWH` has `X64WakeWcRes.WcResW`'s fields (`bl`, `res`; no `f`).
- The landing is re-based to `R.fp (-8)` (`bXRH_rebase`), as in x86-64 wake; AArch64 has a single `sp`-based
  frame.
- The reserve's entry is wake's `X64WakeWcRes.rNe` (it depends only on the labels), not a new `rNeH`.
-/
import Spike.Lib.X64HelloWcPre
import Spike.Lib.X64WakeWcRes

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.WakeWc (AGB WX SN RsN BoxW boxSt rNe reserveW_mono)
open Spike.Lib.X64.Rt.Reserve (ResG RN rvN rvX ResOkA ReserveW reserve_segWA)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The blocks, the rows and the checks -/

/-- `.x22`'s block: the cell to `-48(%rbp)`, the cell back, the box's word `0`. -/
def wcS0H : List (Directive × Nat) := (parse("movq %rax, -48(%rbp)
movq -48(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]

block_spec wcS0H (-136) 8 oWRH wcS0H

/-- **`.x22`'s block and the box's store in `cells`**: the block at `0`, the store at `15`. -/
def wcS0InH (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.x0" 0 wcS0H && blockAtB cells ".Lwc_main.x0" 15 boxSt

theorem hello_wcS0InH : wcS0InH SccCode.helloCells = true := by decide +kernel

/-- The reserve's call. -/
def resBH : List (Directive × Nat) := (parse("call scc_rt_thread_reserve")).zip [5]

block_spec resBH (-136) 16 (⟨-128, [(.rbp, 0)]⟩ : SO) resBH

/-- **The call in `cells`**: at `.x22`'s `18`, `.x23` right after. -/
def wcResInH (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.x0" 18 resBH && labelGapB cells ".Lwc_main.x0" ".Lwc_main.x1" 23

theorem hello_wcResInH : wcResInH SccCode.helloCells = true := by decide +kernel

theorem hello_reserveIn : Flow.Reserve.reserveIn SccCode.helloCells = true := by decide +kernel

/-! ## `.x22` to the box's store -/

/-- **`wcJH`'s frame facts on `R.fp (-8)`**: the return address at `8`, the caller's `%rbp` at `0`, the five
spilled argument words at `-8 .. -40`. -/
def wcJFH (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot 8 = σe.slot 0 ∧ σ.slot 0 = σe.regs.rbp.toBitVec ∧
    σ.slot (-8) = σe.regs.rdi.toBitVec ∧ σ.slot (-16) = σe.regs.rsi.toBitVec ∧
    σ.slot (-24) = σe.regs.rdx.toBitVec ∧ σ.slot (-32) = σe.regs.rcx.toBitVec ∧ σ.slot (-40) = σe.regs.r8.toBitVec

section Sp0

variable (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J1 : AS → Ctl → Prop)

/-- **The nodes**: `.x22` (the allocator's return, `wXH .x18`, with `%rbp`'s offset) and the box's store (`%rax`
the word `0`, `%rcx` and slot `-56` the cell, the hold kept). -/
def sNH : SN → ND
  | .b => ⟨lab ".Lwc_main.x0", oWRH, (wXH ms lab R J1 .x18).J⟩
  | .st => ⟨lab ".Lwc_main.x0" + Int64.ofNat 15, oWRH, fun σ c => ∃ q : AGB ms lab, ∃ o : BitVec 64,
      wcJH J1 σ q.1.c0 ∧ c = holdCtr ms q.1.c0 o ∧ σ.regs.rax.toBitVec = 0#64 ∧
      σ.regs.rcx.toBitVec = σ.slot (-56) ∧ (σ.slot (-56)).toNat = ms.heap + 16 * o.toNat + ms.off 1 q.1.τ ∧
      o.toNat + ms.units 1 q.1.τ ≤ ms.cells ∧ ms.lo o.toNat⟩

end Sp0

section Land

variable (ms : MemSide isa) (lab : Label → Int64) (J1 : AS → Ctl → Prop)

/-- **The landing past the box's store on `R`** for the fresh label `l` at the cell `A`, at `oWRH` (the cell at
slot `-56`). -/
def bXRH (l : WeakMem.AllocLabel) (A : Nat) : ND :=
  ⟨lab ".Lwc_main.x0" + Int64.ofNat 18, oWRH, fun σ c => ∃ q : AGB ms lab,
    wcJH J1 σ q.1.c0 ∧ (σ.slot (-56)).toNat = A ∧
    c = ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ ∧
    ∃ o : Nat, A = ms.heap + 16 * o + ms.off 1 q.1.τ ∧ o + ms.units 1 q.1.τ ≤ ms.cells⟩

/-- **The landing past the box's store** on `R.fp (-8)` (the frame based at the saved `%rbp`, `oWH`) for the
fresh label `l` at the cell `A`: the source past its `new` (`o` bound to `l`'s owned pointer, no hold), the cell
at `-48`, the frame kept (`wcJFH`); the cell the allocator's, `ms.heap + 16·o + ms.off 1 τ` for a counter value
`o` within the cells. -/
def bXH (l : WeakMem.AllocLabel) (A : Nat) : ND :=
  ⟨lab ".Lwc_main.x0" + Int64.ofNat 18, ⟨-128, [(.rbp, 0)]⟩, fun σ c => ∃ q : AGB ms lab,
    wcJFH J1 σ q.1.c0 ∧ (σ.slot (-48)).toNat = A ∧
    c = ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ ∧
    ∃ o : Nat, A = ms.heap + 16 * o + ms.off 1 q.1.τ ∧ o + ms.units 1 q.1.τ ≤ ms.cells⟩

end Land

/-- **The offsets of `wc_main`'s body from the return address's base** (frame 128): `⟨-128, [(.rbp, 0)]⟩` on
`R.fp (-8)` is `⟨-136, [(.rbp, -8)]⟩` on `R`. -/
theorem so_rebase_wcMainH (r : Reg64) (k : Int) (h : SO.get ⟨-128, [(.rbp, 0)]⟩ r = some k) :
    SO.get ⟨-136, [(.rbp, -8)]⟩ r = some (-8 + k) := by
  unfold SO.get at h ⊢
  split at h
  · cases h; simp_all
  · rename_i hr
    simp only [hr, ↓reduceIte]
    simp only [lk] at h ⊢
    split at h
    · cases h; simp_all
    · cases h

/-- **The landing re-based**: a pair at `bXRH l A` on `R` is at `bXH l A` on `R.fp (-8)` (`At.rebase` at
`d = -8`). -/
theorem bXRH_rebase {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {lab : Label → Int64} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl} (h : At exe endPc R F (bXRH ms lab J1 l A) s c) :
    At exe endPc (R.fp (-8)) F (bXH ms lab J1 l A) s c :=
  At.rebase (d := -8) (n := bXRH ms lab J1 l A) (n' := bXH ms lab J1 l A) (by decide) rfl
    so_rebase_wcMainH
    (fun σ c ⟨q, ⟨σe, hJe, h0, h8, h16, h24, h32, h40, h48⟩, hA, hc, ho⟩ =>
      ⟨q, ⟨σe, hJe, by simpa [enter] using h0, by simpa [enter] using h8, by simpa [enter] using h16,
        by simpa [enter] using h24, by simpa [enter] using h32, by simpa [enter] using h40,
        by simpa [enter] using h48⟩, by simpa [enter] using hA, hc, ho⟩) h

/-- **`.x22`'s states inside `W`**, none moved by `K`: the block's and the store's. -/
structure WcSp0WH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J1 : AS → Ctl → Prop) : Prop where
  b : BlkW W K exe endPc R F (sNH ms (_root_.Executable.labels exe).label R J1 .b) wcS0H
  st : NodeW W K exe endPc R F (sNH ms (_root_.Executable.labels exe).label R J1 .st)

/-- `.x22` is inside the trivial predicate, with no outside moves. -/
theorem WcSp0WH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J1 : AS → Ctl → Prop} :
    WcSp0WH (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J1 :=
  ⟨BlkW.triv, NodeW.triv⟩

section Sp0Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` at `.x22` is one segment inside `W`** in any valid layout of `helloCells`: from the allocator's
return at a box allocation (`wXH .x18`) to the box's store, where the source takes its `new` and every fresh
label's landing `bXH l A` on `R.fp (-8)` is one `ms.xa` continues in (`hxa`); the segment has no other exit
(`Q` any).
- The value boxed is one word represented by `0` (`hbox`).
- Every cell the allocator may return is mapped for writing and unmapped in private memory under `F` (`hcell`).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_wc_sp0_segW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {J1 : AS → Ctl → Prop} (hW : WcSp0WH W K exe endPc R F ms J1)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) →
      ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none →
      At exe endPc (R.fp (-8)) F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F (wXH ms (_root_.Executable.labels exe).label R J1 .x18)) Q := by
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h15⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine ((fn_segW (N := sNH ms lab R J1) (E := fun x : Empty => x.elim) (fun i => ?_) SN.b).mono_post
    fun _ _ ⟨x, _⟩ => x.elim).mono_pre
    fun _ _ h => Hello1.At.rbp_addr (J := (wXH ms lab R J1 .x18).J) h fun _ _ ⟨_, _, hb, _⟩ => hb
  cases i
  case b =>
    refine seg_ndW (by simp [wcS0H]) wcS0H_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.b
      fun σ c hJ => ⟨c, .refl c, .inl ⟨SN.st, ?_, ?_, ?_⟩⟩
    · simp only [sNH]; rw [wcS0H_run]; rfl
    · simp only [sNH]; rw [wcS0H_run]; rfl
    · simp only [sNH, wXH] at hJ ⊢
      rw [wcS0H_run]
      obtain ⟨q, ⟨σe, hJe, h0', h8, h16, h24, h32, h40, h48⟩, -, o, hc, hx0, hle, hlo', -⟩ := hJ
      have h1 := q.2.one
      rw [h1] at hx0 hle
      refine ⟨q, o, ⟨σe, hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hc, ?_, ?_, ?_, hle, hlo'⟩
      · simp [Spike.Lib.upd, h0']
      · simp [Spike.Lib.upd, h8]
      · simp [Spike.Lib.upd, h16]
      · simp [Spike.Lib.upd, h24]
      · simp [Spike.Lib.upd, h32]
      · simp [Spike.Lib.upd, h40]
      · simp [Spike.Lib.upd, h48]
      · simp [Reg64s.set64]
      · simp [Spike.Lib.upd, Reg64s.set64, Reg64s.get64]
      · simpa [Spike.Lib.upd, Reg64s.get64] using hx0
  case st =>
    refine Alloc.newStore_ndW (b := .rcx) (r := .rax) (k := 0) (z := 3)
      (fun l A => bXRH ms lab J1 l A) (code_field hp hend h15 rfl)
      (fun l A s c hl h => hxa l A s c hl (bXRH_rebase h)) hW.st fun m σ c hA hD hJ => ?_
    obtain ⟨q, o, hwc, rfl, h0, hcx, hA56, hle, hlo'⟩ := hJ
    have hj : ∃ σ, J1 σ q.1.c0 := let ⟨σe, hJe, _⟩ := hwc; ⟨σe, hJe⟩
    obtain ⟨w, hws, hacc, hrep⟩ := hbox q hj
    have ha : bAddr σ.regs .rcx 0 = σ.slot (-56) := by
      rw [← hcx]; simp [bAddr, Reg64s.get64]
    have ha' : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 (ms.heap + 16 * o.toNat + ms.off 1 q.1.τ) := by
      rw [ha, ← hA56, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    obtain ⟨hmp, hun⟩ := hcell q hj o.toNat hlo' hle
    refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o.toNat),
      o.toNat, q.2.term, hws ▸ q.2.ev, hacc, ?_, rfl, rfl, by rw [ha, hA56], hle, fun l _ => ⟨?_, rfl, q, hwc,
      by rw [ha], rfl, o.toNat, by rw [ha, hA56], hle⟩⟩
    · have : (σ.regs.get64 .rax).toNat = 0 := by simp [Reg64s.get64, h0]
      rw [this]; exact hrep
    · show lab ".Lwc_main.x0" + Int64.ofNat 18 = lab ".Lwc_main.x0" + Int64.ofNat 15 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl

end Sp0Seg

/-! ## The box's store's landing to `.x23` -/

/-- **`bXH`'s facts depend only on the slots `-48 … 8`.** -/
theorem bXH_slots {ms : MemSide isa} {lab : Label → Int64} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel}
    {A : Nat} {σ σ' : AS} {c : Ctl} (h : (bXH ms lab J1 l A).J σ c)
    (hs : ∀ k : Int, -48 ≤ k → k ≤ 8 → k % 8 = 0 → σ'.slot k = σ.slot k) : (bXH ms lab J1 l A).J σ' c := by
  obtain ⟨q, ⟨σe, hJe, h8, h0, hm8, hm16, hm24, hm32, hm40⟩, hA, hc, ho⟩ := h
  refine ⟨q, ⟨σe, hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hc, ho⟩
  · rw [hs 8 (by decide) (by decide) (by decide), h8]
  · rw [hs 0 (by decide) (by decide) (by decide), h0]
  · rw [hs (-8) (by decide) (by decide) (by decide), hm8]
  · rw [hs (-16) (by decide) (by decide) (by decide), hm16]
  · rw [hs (-24) (by decide) (by decide) (by decide), hm24]
  · rw [hs (-32) (by decide) (by decide) (by decide), hm32]
  · rw [hs (-40) (by decide) (by decide) (by decide), hm40]
  · rw [hs (-48) (by decide) (by decide) (by decide), hA]

section Res

variable (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J1 : AS → Ctl → Prop)
  (Q : WeakMem.AllocLabel → Nat → Ctl → Prop)

/-- **The source and frame past the box's store**: some fresh label's landing facts (`bXH l A`) with the source
at `Q l A`. -/
def rJH (σ : AS) (c : Ctl) : Prop := ∃ l A, (bXH ms lab J1 l A).J σ c ∧ Q l A c

/-- **The nodes**: the call block (the landing past the box's store, `%rbp` at the saved `%rbp`) and the
reserve's entry (`.x23` pushed at `-136`). -/
def rNH : RsN → ND
  | .bl => ⟨lab ".Lwc_main.x0" + Int64.ofNat 18, ⟨-128, [(.rbp, 0)]⟩, fun σ c =>
      rJH ms lab J1 Q σ c ∧ σ.regs.get64 .rbp = R.addr 0⟩
  | .call => ⟨lab "scc_rt_thread_reserve", ⟨-136, []⟩, fun σ c => rJH ms lab J1 Q σ c ∧
      σ.regs.get64 .rbp = R.addr 0 ∧ σ.slot (-136) = (lab ".Lwc_main.x1").toBitVec⟩

/-- **The exit at `.x23`**: the reserve's result `1` in `%rax`, the source and frame kept, `%rbp` at the saved
`%rbp`. -/
def rXH : Unit → ND
  | () => ⟨lab ".Lwc_main.x1", ⟨-128, []⟩, fun σ c => rJH ms lab J1 Q σ c ∧
      σ.regs.get64 .rbp = R.addr 0 ∧ σ.regs.rax.toBitVec = 1#64⟩

end Res

/-- The reserve's region at the call: based at the pushed return address (`-136`), its frame of 32 and saved
`%rbp` below, the return address above. -/
abbrev rARH (R : Region) : Region := R.callee (-136) (-40) 8

/-- **The reserve's call context in `wc_main`'s region `R`** at the memory `m`, for the ghosts `g`. -/
def ResCtxH (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (g : Flow.Ret0.AllocTcb.G × Ctl)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-136, []⟩ mC σC ∧ Jc σC c ∧ (rNe lab g).J (enter (-136) σC) c ∧ CKept R (-136) (-40) 8 mC m

/-- **`wc_main`'s states from the call block to `.x23` inside `W`**, none moved by `K`: the call block's, and
the reserve's in its region (at the counter's old value `0`, returning to `.x23`). -/
structure WcResWH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J1 : AS → Ctl → Prop)
    (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  bl : BlkW W K exe endPc R F (rNH ms (_root_.Executable.labels exe).label R J1 Q .bl) resBH
  res : ∀ g : Flow.Ret0.AllocTcb.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x1").toBitVec →
    ∀ i, ReserveW W K exe endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH (_root_.Executable.labels exe).label R
        (rNH ms (_root_.Executable.labels exe).label R J1 Q .call).J g m) ⟨g.1, 0#64, g.2⟩ i

/-- From the call block to `.x23` inside the trivial predicate, with no outside moves. -/
theorem WcResWH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcResWH (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J1 Q := by
  refine ⟨BlkW.triv, fun _ _ i => ?_⟩
  cases i <;> dsimp only [ReserveW] <;> first | exact BlkW.triv | exact NodeW.triv

section ResSeg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from the box's store to `.x23` is one segment inside `W`** in any valid layout of `helloCells`:
from the landing past the box's store (`bXH l A` on `R`, some fresh label `l`, the source at `Q l A`) to `.x23`
(`rXH`).
- The reserve runs at the counter's old value `0` (`hres`), returning `1`.
- The source takes no step (its publication is at `.x25`'s `mfence`; see the module docstring).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_wc_res_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -176) (hhi : 16 ≤ R.hi)
    {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hW : WcResWH W K exe endPc R F ms J1 Q)
    (hres : ∀ g : Flow.Ret0.AllocTcb.G × Ctl, ResOkA ms F exe endPc (rARH R) F ⟨g.1, 0#64, g.2⟩) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c)
      (fun s c => ∃ x, At exe endPc R F (rXH ms (_root_.Executable.labels exe).label R J1 Q x) s c) := by
  have hin := hello_wcResInH
  simp only [wcResInH, Bool.and_eq_true] at hin
  obtain ⟨h18, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e23 : lab ".Lwc_main.x1" = lab ".Lwc_main.x0" + Int64.ofNat 23 := label_labelGapB hp hgap
  refine (fn_segW (N := rNH ms lab R J1 Q) (E := rXH ms lab R J1 Q) (fun i => ?_) RsN.bl).mono_pre ?_
  rotate_left
  · rintro s c ⟨l, A, h, hQ⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hb⟩ := Hello1.At.reg_addr (r := .rbp) (k := 0) rfl h
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨l, A, hJ, hQ⟩, hb⟩
  cases i
  case bl =>
    refine seg_ndW (by simp [resBH]) resBH_ok hF hR (by omega) hhi (code_field hp hend h18 rfl) hW.bl
      fun σ c hJ => ⟨c, .refl c, .inl ⟨RsN.call, ?_, ?_, ?_⟩⟩
    · simp only [rNH]; rw [resBH_run]
    · simp only [rNH]; rw [resBH_run]; rfl
    · simp only [rNH] at hJ ⊢
      rw [resBH_run]
      obtain ⟨⟨l, A, hX, hQ⟩, hb⟩ := hJ
      refine ⟨⟨l, A, bXH_slots hX fun k h1 h2 h3 => ?_, hQ⟩, ?_, ?_⟩
      · have hk : ¬ k = -136 := by omega
        simp only [upd_apply, hk, ↓reduceIte]
      · simpa [Reg64s.set64, Reg64s.get64] using hb
      · rw [e23]
        simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add, BitVec.add_assoc]
        rfl
  case call =>
    refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -40) (hi' := 8) (M := fun _ => True)
      (Ne := rNe lab) (Ex := fun g : Flow.Ret0.AllocTcb.G × Ctl => rvX ⟨g.1, 0#64, g.2⟩)
      hR hF (by show R.lo ≤ -136 - 0 + -40; omega) (by decide) (by show (-136 : Int) - 0 < R.hi; omega)
      (by show (-136 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-136 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, h136⟩, ⟨-, -, -, hra⟩⟩ := hg
        have hr : g.1.ra = (lab ".Lwc_main.x1").toBitVec := by
          rw [← hra, ← h136]; rfl
        exact (reserve_segWA hp hend hello_reserveIn hF' hR' hlo' hhi' hFF ⟨g.1, 0#64, g.2⟩
          (by show (0#64 : BitVec 64).toNat + 1 ≤ 1023; decide) ((hres g).mono hFF)
          fun i => reserveW_mono (hW.res g hr i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c -
      exact ⟨(⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-136 - 0 + 0)⟩, c), rfl, rfl, rfl, rfl, rfl⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨l, A, hX, hQ⟩, hb, h136⟩ ⟨hc, -, hfp, hra⟩ ⟨hc', hpost⟩ hreg - - hsl
      have hkeep : ∀ k : Int, -48 ≤ k → k ≤ 8 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rNH]; omega)
      refine .inr ⟨(), ?_, by show SO.le ⟨-128, []⟩ ⟨-136 - 0 + 8, []⟩ = true; decide,
        ⟨l, A, hc' ▸ hc ▸ bXH_slots hX hkeep, hc' ▸ hc ▸ hQ⟩, ?_, ?_⟩
      · show lab ".Lwc_main.x1" = Int64.ofBitVec g.1.ra
        rw [← hra]
        show _ = Int64.ofBitVec (σC.slot (-136 - 0 + 0))
        rw [show (-136 : Int) - 0 + 0 = -136 by decide, h136, int64_ofBitVec_toBitVec]
      · rw [← hb]
        simp only [Reg64s.get64]
        rw [hreg, hpost.2.1, ← hfp]; rfl
      · rw [hreg, Rt.Reserve.post_rax hpost]; rfl

end ResSeg

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wcS0InH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wcS0InH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wcResInH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wcResInH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_reserveIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_reserveIn

/-- info: 'Spike.Lib.X64.Flow.HelloWc.bXRH_rebase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.bXRH_rebase

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_sp0_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_sp0_segW

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_res_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_res_segW
