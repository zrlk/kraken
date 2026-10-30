/-
**`wc_worker`'s head on AArch64, with the thread rows** (the worker's half): `hello.w`'s `wc_worker` (`scc --arch arm -o -
Scc/Test/hello.w`) from `.L23_wc_worker.0_entry` (after its prologue, `sp`
at the frame's base, offset `-96`; the arguments `x0..x5` in the words at
`-96..-56`, `x29`/`x30` at `-16`/`-8`) to `.L23_wc_worker.sp4`, past the
call of hello's fenced `scc_rt_print` (`PrintF.printF_callT`).

The `.0_entry` block (`wkE`) is `hello1`'s `wcE` with the scratch words
moved up by 8 (they sit above the worker's six argument words): it computes
`print`'s buffer `x0 = b + lo32(o)` and count `x1 = min(n, 8·m)` (`b`, `o`,
`m`, `n` the words at `-96`, `-88`, `-80`, `-72`), writes only the words
`-48..-24`, and calls `scc_rt_print` with the return address `.sp4`.

- `wkE`, `wkE_ok`, `wkE_run`; `wkSl` (the frame's words after the block),
  `wkSl_eq`, `wkSl_keep` (the record and the tail's words `c`/`j` at
  `-64`/`-56` are kept); `wkC` (the call state, irreducible), `wkC_eq`,
  `wkE_X30`, `wkC_tp`, `wkC_x1`, `wkC_x1_lt`, `wkC_x0`;
- `seg_wkBodyT`: the head as one `SegT` segment, from `.0_entry` to the
  caller's node `x` at `.sp4` or `print`'s abort. The source's entry to
  `print` (`hcall`, a local run to `print`'s predicate `Pr` at 0 bytes) and
  the return (`hedge`: `x`'s invariant from `Pr` at all bytes, the frame's
  words, the thread pointer) are the caller's; so is `print`'s write system
  call (`hsvc`, `FA.hsvc_of_emitT` gives it from the output row).
- `seg_wkT`: the head then the tail from `.sp4` (a hypothesis `htail`,
  `WkTail.seg_wkTailU`'s conclusion), via `SegT.seq_or`.
- `ThrHead.seg_thrHeadT`: `scc_rt_thr_worker`'s `.0_entry` block (`thE`)
  and its call of `wc_worker` (`call_ndT`, `wc_worker`'s segment given in
  every region `[-144, 0)` below the frame of 80).
-/
import Spike.Lib.A64PrintF
import Spike.Lib.A64Alloc

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.Flow.Worker.Body

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Alloc (subs_c)

/-! ## The `.0_entry` block -/

/-- `wc_worker`'s `.0_entry` block: `print`'s arguments from the frame's
words, then the call. -/
def wkE : List Directive := parseAArch64("ldr x9, [sp, #8]
ubfm x9, x9, #0, #31
str x9, [sp, #48]
ldr x9, [sp]
ldr x10, [sp, #48]
add x9, x9, x10
str x9, [sp, #56]
ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #64]
ldr x9, [sp, #24]
ldr x10, [sp, #64]
subs xzr, x9, x10
ldr x11, [sp, #24]
ldr x12, [sp, #64]
csel x9, x11, x12, lo
str x9, [sp, #72]
ldr x0, [sp, #56]
ldr x1, [sp, #72]
bl scc_rt_print")

block_spec wkE (-144) 0 (⟨-96, []⟩ : SO) wkE

/-- The frame's words after the `.0_entry` block from `σ`. -/
def wkSl (σ : AS) : Int → BitVec 64 := (arun (fun _ => 0) wkE ⟨0, ⟨-96, []⟩, σ⟩).σ.slot

theorem wkSl_eq (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab wkE ⟨pc, ⟨-96, []⟩, σ⟩).σ.slot = wkSl σ := by
  rw [wkSl, wkE_run, wkE_run]

/-- The block keeps the frame record and the tail's words `c`, `j`. -/
theorem wkSl_keep (σ : AS) : wkSl σ (-16) = σ.slot (-16) ∧ wkSl σ (-8) = σ.slot (-8) ∧
    wkSl σ (-64) = σ.slot (-64) ∧ wkSl σ (-56) = σ.slot (-56) := by
  simp only [wkSl, wkE_run]
  exact ⟨by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply],
    by simp [Spike.Lib.upd_apply]⟩

/-- The abstract state at `print`'s entry, after the `.0_entry` block from
`σ` (irreducible: the block's closed form is large). -/
@[irreducible] def wkC (lab : Label → Int64) (σ : AS) : AS :=
  (arun lab wkE ⟨lab ".L23_wc_worker.0_entry", ⟨-96, []⟩, σ⟩).σ

theorem wkC_eq (lab : Label → Int64) (σ : AS) :
    wkC lab σ = (arun lab wkE ⟨lab ".L23_wc_worker.0_entry", ⟨-96, []⟩, σ⟩).σ := by
  unfold wkC; rfl

/-- The block's call leaves the return address `21` instructions on. -/
theorem wkE_X30 (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab wkE ⟨pc, ⟨-96, []⟩, σ⟩).σ.regs.X30.toBitVec = (pc + Int64.ofNat (4 * 21)).toBitVec := by
  rw [wkE_run]
  show BitVec.ofInt 64 _ = _
  rw [Ret0.ofInt_bmod]
  simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

/-- The block keeps the thread pointer. -/
theorem wkC_tp (lab : Label → Int64) (σ : AS) : (wkC lab σ).regs.TPIDR_EL0 = σ.regs.TPIDR_EL0 := by
  rw [wkC_eq, arun_tpidr]

/-- **The byte count**: `min(n, m·8)`. -/
theorem wkC_x1 (lab : Label → Int64) (σ : AS) :
    (wkC lab σ).regs.X1.toBitVec.toNat = min (σ.slot (-72)).toNat (σ.slot (-80) * 8#64).toNat := by
  rw [wkC_eq, wkE_run]
  simp only [subs_c]
  by_cases h : (σ.slot (-80) * 8#64).toNat ≤ (σ.slot (-72)).toNat
  · simp only [h, decide_true, Bool.true_eq_false, ite_false]; omega
  · simp only [h, decide_false, ite_true]; omega

/-- The count is below `2^63` when `8·m` is. -/
theorem wkC_x1_lt (lab : Label → Int64) (σ : AS) (hm : (σ.slot (-80)).toNat * 8 < 2 ^ 63) :
    (wkC lab σ).regs.X1.toBitVec.toNat < 2 ^ 63 := by
  rw [wkC_x1]
  have : (σ.slot (-80) * 8#64).toNat = (σ.slot (-80)).toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; omega
  omega

/-- **The buffer**: the slice's base plus the offset's low word. -/
theorem wkC_x0 (lab : Label → Int64) (σ : AS) :
    (wkC lab σ).regs.X0.toBitVec = σ.slot (-96) + BitVec.setWidth 64 ((σ.slot (-88)).take 32) := by
  rw [wkC_eq, wkE_run]; rfl

/-! ## The head -/

/-- The head's internal nodes. -/
inductive WN where
  | e | call

/-- The head's exits. -/
inductive WX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (J : AS → Ctl → Prop) (Pr Qa : AS → Nat → Ctl → Prop) (x : ND)

/-- **The head's nodes**, from the invariant `J` at `.0_entry`; at the
call, the source at `print`'s predicate `Pr` of the call state at 0
bytes. -/
def wN : WN → ND
  | .e => ⟨lab ".L23_wc_worker.0_entry", ⟨-96, []⟩, J⟩
  | .call => ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => (∃ σ0 c0, J σ0 c0 ∧ σ = wkC lab σ0) ∧ Pr σ 0 c⟩

/-- **The head's exits**: the caller's node `x` (at `.sp4`), and `print`'s
abort. -/
def wX : WX → ND
  | .ret => x
  | .abort => ⟨lab "scc_rt_abort", ⟨-144, []⟩, fun σ c => σ.regs.X0 = 4 ∧ ∃ σC k, Qa σC k c⟩

end Spec

section Proof

/-- **Sequencing on one branch**: a segment to `Q ∨ X`, then one from `Q`
to `Y`, is one to `Y ∨ X` (the `X` exits pass through). -/
theorem _root_.Spike.Lib.SegT.seq_or {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide I} {P Q X Y : Frag I} (h₁ : SegT p lbl ms P (fun s c => Q s c ∨ X s c))
    (h₂ : SegT p lbl ms Q Y) : SegT p lbl ms P (fun s c => Y s c ∨ X s c) := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr (hs₂ s c h))
      · exact .inr (.inr h)
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`wc_worker`'s head is one segment with the thread rows**, from
`.0_entry` (invariant `J`) to the caller's node `x` (pc `.sp4`, `hxpc`;
offsets `⟨-96, []⟩`, `hxo`) or `print`'s abort: the `.0_entry` block (the
source takes the local run `hcall` into `print`, to `Pr` at 0 bytes), then
the call of hello's fenced `scc_rt_print` (`PrintF.printF_callT`, `print`
in the 48 bytes below the frame: the region reaches `-144`). At the return
`x`'s invariant holds of every state whose frame words are as the block
left them and whose thread pointer is the entry's, the source at `Pr` with
all `x1` bytes out (`hedge`). The code is `hcodeE` (the block), `hgap`
(`.sp4` right after it), `hcode`/`hentry` (`print`'s); `print`'s write
system call is `hsvc` (in `PrintF.cN`'s form). -/
theorem seg_wkBodyT (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {Pr Qa : AS → Nat → Ctl → Prop} {x : ND}
    (hxpc : x.pc = (_root_.Executable.labels exe).label ".L23_wc_worker.sp4") (hxo : x.o = ⟨-96, []⟩)
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".L23_wc_worker.0_entry") wkE)
    (hgap : (_root_.Executable.labels exe).label ".L23_wc_worker.sp4" =
      (_root_.Executable.labels exe).label ".L23_wc_worker.0_entry" + Int64.ofNat (4 * 21))
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hm : ∀ σ c, J σ c → (σ.slot (-80)).toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ Pr (wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (wN (_root_.Executable.labels exe).label J Pr .call).J σC c →
      SegT p lbl ms (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hedge : ∀ σ0 c0, J σ0 c0 → ∀ (σR : AS) c',
      Pr (wkC (_root_.Executable.labels exe).label σ0)
        (wkC (_root_.Executable.labels exe).label σ0).regs.X1.toBitVec.toNat c' →
      (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = wkSl σ0 k) →
      σR.regs.TPIDR_EL0 = σ0.regs.TPIDR_EL0 → x.J σR c') :
    SegT p lbl ms (At exe endPc R F (wN (_root_.Executable.labels exe).label J Pr .e))
      (fun s c => ∃ y, At exe endPc R F (wX (_root_.Executable.labels exe).label Qa x y) s c) := by
  let lab := (_root_.Executable.labels exe).label
  refine fn_segT (N := wN lab J Pr) (E := wX lab Qa x) (fun i => ?_) WN.e
  cases i
  case e =>
    refine Seg.toT (seg_nd (by simp [wkE]) wkE_ok hF hR hal hlo hhi hcodeE fun σ c hJ => ?_)
    obtain ⟨c', hr, hP⟩ := hcall σ c hJ
    refine ⟨c', hr, .inl ⟨WN.call, ?_, ?_, ⟨σ, c, hJ, (wkC_eq _ _).symm⟩, ?_⟩⟩
    · simp only [wN]; rw [wkE_run]
    · simp only [wN]; rw [wkE_run]; rfl
    · show Pr (arun lab wkE ⟨lab ".L23_wc_worker.0_entry", ⟨-96, []⟩, σ⟩).σ 0 c'
      rw [← wkC_eq]; exact hP
  case call =>
    refine PrintF.printF_callT (nC := wN lab J Pr .call) (Pc := Pr) (Qc := Qa) hR hal hF
      (by show R.lo ≤ -96 + -48; omega) (by show (-96 : Int) < R.hi; omega) (by show (-96 : Int) % 16 = 0; decide) hcode hentry rfl
      (fun σ c h => h.2) (fun σ c ⟨⟨σ0, c0, hJ0, hσ⟩, _⟩ => hσ ▸ wkC_x1_lt lab σ0 (hm σ0 c0 hJ0)) hsvc ?_ ?_
    · rintro σC c σR c' ⟨⟨σ0, c0, hJ0, rfl⟩, -⟩ - - htp hP hsl
      refine .inr ⟨WX.ret, ?_, ?_, ?_⟩
      · show x.pc = Int64.ofBitVec (wkC lab σ0).regs.X30.toBitVec
        rw [hxpc, wkC_eq, wkE_X30, ← hgap, int64_ofBitVec_toBitVec]
      · show x.o.le ⟨-96, []⟩ = true
        rw [hxo]; rfl
      · refine hedge σ0 c0 hJ0 σR c' hP (fun k h1 h2 h3 => ?_) (by rw [htp, wkC_tp])
        rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), wkC_eq,
          wkSl_eq]
    · rintro σC c σR c' k - h4 hQ -
      exact .inr ⟨WX.abort, rfl, rfl, h4, σC, k, hQ⟩

/-- **`wc_worker` from `.0_entry` to its return**, the head (`seg_wkBodyT`)
then the tail from `.sp4` (`htail`: `WkTail.seg_wkTailU` for the ghosts
`c1 c2 A B x29 ra tp`, the source at `cw` after `print`'s return): at the
return the source is past its `unpark` (`WkTail.E`), or `print` aborted.
`hrec` gives the tail's invariant at `.sp4` from the entry's: the frame
record, `c`/`j`'s words and the thread pointer (kept by the block and by
`print`), and the source at `cw` once `print` is done. -/
theorem seg_wkT (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {Pr Qa : AS → Nat → Ctl → Prop}
    {cw c1 c2 : Ctl} {A B x29 ra tp : BitVec 64}
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".L23_wc_worker.0_entry") wkE)
    (hgap : (_root_.Executable.labels exe).label ".L23_wc_worker.sp4" =
      (_root_.Executable.labels exe).label ".L23_wc_worker.0_entry" + Int64.ofNat (4 * 21))
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hm : ∀ σ c, J σ c → (σ.slot (-80)).toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ Pr (wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (wN (_root_.Executable.labels exe).label J Pr .call).J σC c →
      SegT p lbl ms (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hrec : ∀ σ0 c0, J σ0 c0 → σ0.slot (-16) = x29 ∧ σ0.slot (-8) = ra ∧ σ0.slot (-64) = A ∧
      σ0.slot (-56) = B ∧ σ0.regs.TPIDR_EL0.toBitVec = tp ∧
      ∀ c', Pr (wkC (_root_.Executable.labels exe).label σ0)
        (wkC (_root_.Executable.labels exe).label σ0).regs.X1.toBitVec.toNat c' → c' = cw)
    (htail : SegT p lbl ms
      (At exe endPc R F (WkTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ y, At exe endPc R F (WkTail.E c2 x29 ra tp y) s c)) :
    SegT p lbl ms (At exe endPc R F (wN (_root_.Executable.labels exe).label J Pr .e))
      (fun s c => (∃ y, At exe endPc R F (WkTail.E c2 x29 ra tp y) s c) ∨
        At exe endPc R F (wX (_root_.Executable.labels exe).label Qa
          (WkTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp .sp4) .abort) s c) := by
  refine (seg_wkBodyT (x := WkTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp .sp4)
    hF hR hal hlo hhi rfl rfl hcodeE hgap hcode hentry hm hcall hsvc ?_).mono_post ?_ |>.seq_or htail
  · intro σ0 c0 hJ0 σR c' hP hsl htp
    obtain ⟨h16, h8, h64, h56, htp0, hc⟩ := hrec σ0 c0 hJ0
    obtain ⟨k16, k8, k64, k56⟩ := wkSl_keep σ0
    refine ⟨hc c' hP, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsl _ (by decide) (by decide) (by decide), k16, h16]
    · rw [hsl _ (by decide) (by decide) (by decide), k8, h8]
    · rw [hsl _ (by decide) (by decide) (by decide), k64, h64]
    · rw [hsl _ (by decide) (by decide) (by decide), k56, h56]
    · rw [htp, htp0]
  · rintro s c ⟨y, h⟩
    cases y
    · exact .inl h
    · exact .inr h

/-! ## `scc_rt_thr_worker`'s head

    .0_entry: x0..x5 = the words at [sp, #0..#40]; bl wc_worker
    .sp0:     (ThrTail)

The frame is `[-80, 0)`; `wc_worker` runs below it, in its own region
`[-144, 0)` from the call's `sp` (its frame of 96 and `print`'s or
`scc_rt_unpark`'s 48 below), so the region reaches `-224`. -/

namespace ThrHead

/-- `scc_rt_thr_worker`'s `.0_entry` block: the arguments, the call. -/
def thE : List Directive := parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
bl wc_worker")

block_spec thE (-224) 0 (⟨-80, []⟩ : SO) thE

/-- The head's internal nodes. -/
inductive TN where
  | e | call

/-- **The head's nodes**, from the invariant `J` at `.0_entry`. -/
def tN (lab : Label → Int64) (J : AS → Ctl → Prop) : TN → ND
  | .e => ⟨lab ".L18_scc_rt_thr_worker.0_entry", ⟨-80, []⟩, J⟩
  | .call => ⟨lab "wc_worker", ⟨-80, []⟩, fun σ c => ∃ σ0, J σ0 c ∧
      σ = (arun lab thE ⟨lab ".L18_scc_rt_thr_worker.0_entry", ⟨-80, []⟩, σ0⟩).σ⟩

/-- **`scc_rt_thr_worker`'s head is one segment with the thread rows**,
from `.0_entry` (invariant `J`) to the caller's nodes `N`/exits `E`: the
block, then the call of `wc_worker` (`call_ndT`, `wc_worker`'s region
`[-144, 0)` below the frame). `wc_worker`'s segment from its entry `Ne g`
to its exits `Ex g` is given for every region holding its frames and every
frame condition giving `F` (`hwk`; `seg_wkT` after `wc_worker`'s prologue);
`hent` picks the ghost at the call, `hret` lands its exits (the return to
`.sp0` is `ThrTail.N .sp0` for the thread tail). -/
theorem seg_thrHeadT {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".L18_scc_rt_thr_worker.0_entry") thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -144 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegT p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN (_root_.Executable.labels exe).label J .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-80) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN (_root_.Executable.labels exe).label J .call).J σC c →
      (Ne g).J (enter (-80) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-80) (-144) 0).Off (k - (-80)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-80 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F (tN (_root_.Executable.labels exe).label J .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (Q := At exe endPc R F (tN lab J .call))
    (Seg.toT (seg_nd (N := fun _ : Unit => tN lab J .call) (E := (nofun : Empty → ND)) (by simp [thE]) thE_ok
      hF hR hal hlo hhi hcodeE fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, rfl⟩⟩) |>.mono_post ?_) ?_
  · simp only [tN]; rw [thE_run]
  · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndT (lo' := -144) (hi' := 0) hR hal hF (by show R.lo ≤ -80 + -144; omega) (by decide)
      (by show (-80 : Int) < R.hi; omega) (by decide) (by show (-80 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end ThrHead

end Proof

end Spike.Lib.A64.Flow.Worker.Body
