/-
**hello.w's thread worker on AArch64: `scc_rt_thr_worker`** (B4a): the target side of `scc_rt_thr_worker` in hello.w's
listing
(`SccCode.helloProg`, `Spike/Lib/A64HelloCode.lean`) over the thread rows
(`OutT`, `SegT`). wake.w's (`Spike.Lib.A64.Flow.Worker.Wake.ThrHeadW`,
`ThrTailW`, `A64WakeWorker.lean`) with hello's packet: the spawn passes six
words (`x0..x5`, the slice's four, the cell, the waiter), so the frame is
`[-80, 0)` (`x0..x5` spilled at `0..40`, `x29`/`x30` at `64`/`72`), the
thread pointer is spilled at `48` and the `exit`'s result at `56`.

    scc_rt_thr_worker: prologue (frame 80, x0..x5 at 0..40)
    .0_entry: x0..x5 = the words at [sp, #0..#40]; bl wc_worker
    .sp0:     x9 = tpidr_el0 (spilled at 48); x10 = x9 + 24
              stlr 1, [x10]                -- the thread's `exited` word
              x0 = 0; x8 = 93
              svc #0                       -- exit: the thread ends

`wc_worker` runs below the frame in its own region `[-192, 0)` from the
call's `sp` (its frame of 96, `scc_rt_print`'s or `scc_rt_unpark`'s 48
below, and `scc_rt_abort`'s 48 below `print` on its abort exit: `rtDepth`'s
worst case 144 + 48), so the thread's region reaches `-272`.

- `HThrTail.seg_thrTail`: the tail from `.sp0` to any fragment.
- `HThrHead.seg_thrHead`: the `.0_entry` block and the call (`call_ndT`),
  `wc_worker`'s segment given in every region `[-192, 0)` (`hwk`).
- `thrIn`, `thrPro`, `hello_thrIn`, `hello_thrPro`: the blocks and the
  prologue decided on `helloProg`; `thrCode`, `thECode`, `hsp0`,
  `thr_prologue_seg`: their consequences in any valid layout of it.
-/
import Spike.Lib.A64WakeWorker
import Spike.Lib.A64HelloCode
import Spike.Lib.A64CodeSegs

namespace Spike.Lib.A64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_thr_worker`'s tail -/

namespace HThrTail

/-- `scc_rt_thr_worker`'s label prefix in hello's listing (wake's). -/
abbrev pfx0 : String := ".L18_scc_rt_thr_worker"

def b0 : List Directive := parseAArch64("mrs x9, tpidr_el0
str x9, [sp, #48]
movz x9, #1
ldr x10, [sp, #48]
add x10, x10, #24")
def b1 : List Directive := parseAArch64("movz x0, #0
movz x8, #93")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-80, []⟩

block_spec b0 (-80) 0 oI b0
block_spec b1 (-80) 0 oI b1

/-- The internal nodes. -/
inductive PN where
  | sp0 | ex | n2 | svc

section Spec

variable (pfx : String) (lab : Label → Int64) (c0 : Ctl) (tp : BitVec 64)

/-- **The nodes.** -/
def N : PN → ND
  | .sp0 => ⟨lab (pfx ++ ".sp0"), oI, fun σ c => c = c0 ∧ σ.regs.TPIDR_EL0.toBitVec = tp⟩
  | .ex => ⟨lab (pfx ++ ".sp0") + 4 + 4 + 4 + 4 + 4, oI, fun σ c => c = c0 ∧
      σ.regs.X10.toBitVec = tp + 24#64 ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .n2 => ⟨lab (pfx ++ ".sp0") + 4 + 4 + 4 + 4 + 4 + 4, oI, fun _ c => c = c0⟩
  | .svc => ⟨lab (pfx ++ ".sp0") + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => c = c0 ∧
      σ.regs.X8 = 93⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp0 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .sp0).pc b0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .ex).pc
      [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .n2).pc b1
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .svc).pc [svcDir]

/-- The code does not depend on the ghosts. -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c0' : Ctl} {tp tp' : BitVec 64}
    (h : Code pfx c0 tp exe endPc) : Code pfx c0' tp' exe endPc :=
  ⟨h.sp0, h.ex, h.n2, h.svc⟩

end Spec

section Proof

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Spike.Lib.upd_apply, Reg64s.getSysReg,
    KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`scc_rt_thr_worker`'s tail is one segment with the thread rows** from
`.sp0` to any fragment: the release of the thread's `exited` word (at
`tp + 24`, `StOk`), then the `exit` with the source at `ret a`
(`OutT.texit`). -/
theorem seg_thrTail {Q : Frag isaLSE2} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code pfx c0 tp exe endPc) :
    SegT p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 tp .sp0)) Q := by
  refine (fn_segT (N := N pfx _ c0 tp) (E := (nofun : Empty → ND)) (fun i => ?_) PN.sp0).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case sp0 => node b0 b0_ok sp0; rw [N, b0_run]; hit PN.ex
  case ex =>
    refine (Spike.Lib.A64.Flow.Ret0.ownStlr_nd (A := tp + 24#64) (fun s he hn => hcode.ex s he hn)
      fun m σ c _ _ hJ => ?_).toT
    obtain ⟨rfl, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, ?_⟩
    hit PN.n2
  case n2 => node b1 b1_ok n2; rw [N, b1_run]; hit PN.svc
  case svc =>
    refine texit_nd hK (fun s he hn => hcode.svc s he hn) fun σ c ⟨hc, h8⟩ => ⟨by rw [h8]; rfl, a, ?_⟩
    rw [hc]; exact ht

end Proof

end HThrTail

/-! ## `scc_rt_thr_worker`'s head -/

namespace HThrHead

/-- `scc_rt_thr_worker`'s `.0_entry` block: the six arguments, the call. -/
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

/-- **The head's nodes**, from the invariant `J` at `.0_entry`; across the
block the source moves from `c0` to `c` with `L c0 c` (a local run: the
worker's split of its argument). -/
def tN (pfx : String) (lab : Label → Int64) (J : AS → Ctl → Prop) (L : Ctl → Ctl → Prop) : TN → ND
  | .e => ⟨lab (pfx ++ ".0_entry"), ⟨-80, []⟩, J⟩
  | .call => ⟨lab "wc_worker", ⟨-80, []⟩, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ L c0 c ∧
      σ = (arun lab thE ⟨lab (pfx ++ ".0_entry"), ⟨-80, []⟩, σ0⟩).σ⟩

section Proof

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_thr_worker`'s head is one segment with the thread rows**,
from `.0_entry` (invariant `J`) to the caller's nodes `N`/exits `E`: the
block, then the call of `wc_worker` (`call_ndT`, `wc_worker`'s region
`[-192, 0)` below the frame). `wc_worker`'s segment from its entry `Ne g`
to its exits `Ex g` is given for every region holding its frames and every
frame condition giving `F` (`hwk`); `hent` picks the ghost at the call,
`hret` lands its exits. The source takes a local run `L` across the block
(`hL`). -/
theorem seg_thrHead {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label (pfx ++ ".0_entry")) thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -192 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegT p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-80) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-80) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-80) (-192) 0).Off (k - (-80)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-80 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (Q := At exe endPc R F (tN pfx lab J L .call))
    (Seg.toT (seg_nd (N := fun _ : Unit => tN pfx lab J L .call) (E := (nofun : Empty → ND)) (by simp [thE])
      thE_ok hF hR hal (Int.le_trans hlo (by decide)) hhi hcodeE fun σ c hJ => ?_) |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndT (lo' := -192) (hi' := 0) hR hal hF (by show R.lo ≤ -80 + -192; omega) (by decide)
      (by show (-80 : Int) < R.hi; omega) (by decide) (by show (-80 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end Proof

end HThrHead

/-! ## The checks on hello's listing -/

/-- `scc_rt_thr_worker`'s blocks at hello's prefix. -/
abbrev thrIn : Bool :=
  blockAt helloProg (HThrTail.pfx0 ++ ".0_entry") 0 HThrHead.thE &&
  labelGap helloProg (HThrTail.pfx0 ++ ".0_entry") (HThrTail.pfx0 ++ ".sp0") 7 &&
  blockAt helloProg (HThrTail.pfx0 ++ ".sp0") 0 HThrTail.b0 &&
  blockAt helloProg (HThrTail.pfx0 ++ ".sp0") 5
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] &&
  blockAt helloProg (HThrTail.pfx0 ++ ".sp0") 6 HThrTail.b1 &&
  blockAt helloProg (HThrTail.pfx0 ++ ".sp0") 8 [svcDir]

/-- The prologue's spills: the six argument registers at `0..40`. -/
abbrev thrPs : List (XReg × Int64) := [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32), (.X5, 40)]

/-- `scc_rt_thr_worker`'s prologue: frame 80, its six arguments at `0..40`. -/
abbrev thrPro : Bool := prologueIn helloProg "scc_rt_thr_worker" (HThrTail.pfx0 ++ ".stack_check")
  (HThrTail.pfx0 ++ ".0_entry") 80 8 (HThrTail.pfx0 ++ ".stack_grow") thrPs

theorem hello_thrIn : thrIn = true := by decide +kernel
theorem hello_thrPro : thrPro = true := by decide +kernel

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
include hp hend

/-- **`scc_rt_thr_worker`'s tail code** at hello's prefix, any ghosts. -/
theorem thrCode {c0 : Ctl} {tp : BitVec 64} : HThrTail.Code HThrTail.pfx0 c0 tp exe endPc := by
  have h := hello_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, h0, h1, h2, h3⟩ := h
  exact ⟨code_of hp hend h0 (by simp only [HThrTail.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h1 (by simp only [HThrTail.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h2 (by simp only [HThrTail.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h3 (by simp only [HThrTail.N, ofNat4_succ, ofNat4_zero])⟩

/-- **`scc_rt_thr_worker`'s `.0_entry` block.** -/
theorem thECode : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".0_entry")) HThrHead.thE := by
  have h := hello_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  exact code_of hp hend h.1 (ofNat4_zero _)

omit hend in
/-- **`.sp0` right after `scc_rt_thr_worker`'s `bl`.** -/
theorem hsp0 : (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") =
    (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".0_entry") + 4 + 4 + 4 + 4 + 4 + 4 + 4 := by
  have h := hello_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGap hp h.2.1]
  simp only [ofNat4_succ, ofNat4_zero]

end Code

/-! ## The prologue -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_thr_worker`'s prologue** in any valid layout of `helloProg`,
with the thread rows: frame 80, `x0..x5` spilled at `0..40`. -/
theorem thr_prologue_seg (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".0_entry"))
    (ho : SO.le nb.o (oFr 80) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (80 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 80 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 80 σ.regs }).regs →
          σ'.slot = stSlots (-(80 : Int64).toInt) σ'.regs thrPs (frSlot σ) → nb.J σ' c) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_of hp hend hello_thrPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge).toT

end Pro

end Spike.Lib.A64.Flow.Worker.Hello

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.HThrTail.seg_thrTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.HThrTail.seg_thrTail

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.HThrHead.seg_thrHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.HThrHead.seg_thrHead

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.thr_prologue_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.thr_prologue_seg
