/-
**wake.w's `scc_rt_main` up to `wc_main`'s entry** (x86-64; twin of
`Spike/Lib/A64WakeMain.lean`; the pre-spawn consumer, hello
plan 1.6): `wake_main_pre_segW`, the segment from `scc_rt_main`'s entry
through its stack-checked prologue (frame 32 under the saved `%rbp`, `%rdi`
saved at `-8(%rbp)`) and its `.entry` block (`movq -8(%rbp), %rdi`,
`call wc_main`) into `wc_main` in its region at the call, followed by a
segment of `wc_main` there (`hWc`, the instance's: `wc_main` does not
return before the `clone`).

wake.w's `main` takes its `ThreadId` (`tidStartT`), so `scc_rt_main`'s
`.entry` reloads the saved `%rdi` before the call: not `mainUIn`'s
one-instruction block (`Spike/Lib/Rt/X64Main.lean`), hence this file.

- `wB0`, `wakeMainIn`, `wake_mainIn`: the block and the code check, decided
  on `wakeCells`;
- `wJd`, `wJ`, `wN0`, `wNC`, `wR`, `wF`, `wJ0`: `scc_rt_main`'s frame, its
  nodes, `wc_main`'s region (depth `D` below the return address),
  frame condition and entry invariant at the call;
- `MainPreWW`: `scc_rt_main`'s own states inside `W` (prologue, call block);
- `wR_ok`, `wake_main_pre_segW`: the region and the segment.

**Unlike AArch64** (`Spike/Lib/X64WakeFrame.lean`): `call` pushes the
return address, so `wc_main` is entered at `wcK = -48` of `scc_rt_main`'s
region with its region `R.callee (-48) (-D) 8` (`WakeFrame.wcR`; AArch64
`R.callee (-48) (-D) 0`) reaching the return address's cell; the frame's
facts are the entry state's return address at offset `0`, its `%rbp` at
`-8`, its `%rdi` at `-16` (AArch64: `x29`, `x30` at `-16`, `-8`, `x0` at
`-48`), `%rsp` `8 + 32` below (`wJd`, the call node's `8` more), and the
call node's return address is the slot at `-48` (AArch64: `x30`). `wN0`
claims `%rbp` (`%rsp + 32`, the prologue's `movq %rsp, %rbp`) and `wNC`
keeps it (`%rsp + 40`), as `X64Main`'s `mainU1R`/`mainUC`. The limit word
is `%fs:8` (`hlimM`, x86-64's `LimOk` at the thread pointer's `+ 8`). No
16-aligned base is asked (`wR_ok`).
-/
import Spike.Lib.Rt.X64Main
import Spike.Lib.X64WakeCode
import Spike.Lib.X64WakeFrame

namespace Spike.Lib.X64.Flow.WakeM

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk seg_oneW)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

/-! ## `scc_rt_main`'s call block -/

/-- `scc_rt_main`'s `.entry` block: the saved `%rdi` (main's `ThreadId`)
back, the call of `wc_main`. -/
def wB0 : List (Directive × Nat) := (parse("movq -8(%rbp), %rdi
call wc_main")).zip [4, 5]

block_spec wB0 (-48) 0 (⟨-40, [(.rbp, -8)]⟩ : SO) wB0

/-- **`scc_rt_main`'s code in `cells`**: the stack-checked prologue (frame
32, the limit at `%fs:8`, `%rdi` at `-8(%rbp)`), `wB0` at `.entry`, `.x2`
right after it. -/
def wakeMainIn (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "scc_rt_main" ".Lscc_rt_main.chk" ".Lscc_rt_main.entry" 32 8 ".Lscc_rt_main.stk" 5 9 3 2 4
      [(.rdi, -8, 4)] &&
    blockAtB cells ".Lscc_rt_main.entry" 0 wB0 &&
    labelGapB cells ".Lscc_rt_main.entry" ".Lscc_rt_main.x2" 9

theorem wake_mainIn : wakeMainIn SccCode.wakeCells = true := by decide +kernel

/-! ## Nodes -/

/-- **`scc_rt_main`'s frame** as some entry state of `J` left it, `%rsp`
`d` more below the frame's base: the return address, the saved `%rbp`, the
saved `%rdi`, `%rsp`, the thread pointer. -/
def wJd (J : AS → Ctl → Prop) (d : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot 0 = σe.slot 0 ∧ σ.slot (-8) = σe.regs.rbp.toBitVec ∧
    σ.slot (-16) = σe.regs.rdi.toBitVec ∧
    σ.regs.rsp.toBitVec = σe.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec - d ∧
    σ.regs.fsBase = σe.regs.fsBase

/-- **`scc_rt_main`'s frame** at its body (`%rsp` at the frame's base). -/
abbrev wJ (J : AS → Ctl → Prop) : AS → Ctl → Prop := wJd J 0#64

section Nodes

variable (lab : Label → Int64) (J : AS → Ctl → Prop)

/-- `scc_rt_main`'s `.entry`, `%rbp` at the saved `%rbp`. -/
def wN0 : ND := ⟨lab ".Lscc_rt_main.entry", ⟨-40, [(.rbp, -8)]⟩, fun σ c =>
  wJ J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)⟩

/-- The call of `wc_main`: `%rdi` the saved `ThreadId`, the return address
`.x2` in the slot at `%rsp`, `%rbp` at the saved `%rbp`. -/
def wNC : ND := ⟨lab "wc_main", ⟨-48, []⟩, fun σ c => wJd J 8#64 σ c ∧
  σ.regs.rdi.toBitVec = σ.slot (-16) ∧ σ.slot (-48) = (lab ".Lscc_rt_main.x2").toBitVec ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -48)⟩

end Nodes

/-- `wc_main`'s region at the call, `D` deep below the return address
(`WakeFrame.wcR`). -/
abbrev wR (R : Region) (D : Int) : Region := R.callee (-48) (-D) 8

example (R : Region) (D : Int) : wR R D = Spike.Lib.X64.WakeFrame.wcR R D := rfl

/-- **`wc_main`'s frame condition at the call** from the caller's state
`m0`, `σC` (`at_enter`). -/
def wF (R : Region) (D : Int) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-48) (-D) 8 m0 m ∧ Abs R ⟨-48, []⟩ m0 σC

/-- `wc_main`'s entry invariant from the caller's state `σC` at the call
node of invariant `Jc`. -/
def wJ0 (Jc : AS → Ctl → Prop) (σC : AS) (σ : AS) (c : Ctl) : Prop := σ = enter (-48) σC ∧ Jc σC c

/-- **`scc_rt_main`'s own states up to the call inside `W`**, none moved by
`K`: its prologue's and the call block's. -/
structure MainPreWW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 32 8
    ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J
  call : BlkW W K exe endPc R F (wN0 (_root_.Executable.labels exe).label J) wB0

/-- `scc_rt_main`'s own states up to the call are inside the trivial
predicate, with no outside moves. -/
theorem MainPreWW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J : AS → Ctl → Prop} :
    MainPreWW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J :=
  ⟨XProW.triv, BlkW.triv⟩

section MainPre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- `wc_main`'s region at the call is a region, its frame condition
stable. -/
theorem wR_ok {D : Int} (hD : 0 ≤ D) (hD8 : D % 8 = 0) (hR : R.OK)
    (hF : FStable R F) (hlo : R.lo ≤ -48 - D) (hhi : 0 ≤ R.hi) (m0 : MachineData) (σC : AS) :
    (wR R D).OK ∧ FStable (wR R D) (wF R D F m0 σC) :=
  ⟨Region.callee_ok hR (by omega) (by omega) (by omega) (by omega),
    fstable_enter hR hF (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

/-- **`scc_rt_main` up to `wc_main`, then `wc_main`, is one segment inside
`W`** in any valid layout of `wakeCells`: from `scc_rt_main`'s entry
(invariant `J`, `%rsp` at the region's offset 0, the return address there)
through its prologue (the limit word's facts for its frame, `hlimM`) and
the call into `wc_main`'s region at the call (`D` deep), then `wc_main`'s
segment there to `Q m0 σC` for every caller's state at the call (`hWc`).
`scc_rt_main`'s states lie in `W`, none moved by `K` (`hW`). -/
theorem wake_main_pre_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {D : Int} (hD : 0 ≤ D) (hD8 : D % 8 = 0)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -48 - D) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} (hW : MainPreWW W K exe endPc R F ms J)
    (hlimM : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec))
    {Q : MachineData → AS → Frag isa}
    (hWc : ∀ m0 σC, (wR R D).OK → FStable (wR R D) (wF R D F m0 σC) →
      SegW W K p lbl ms (At exe endPc (wR R D) (wF R D F m0 σC)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wJ0 (wNC (_root_.Executable.labels exe).label J).J σC⟩) (Q m0 σC)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => ∃ m0 σC, Q m0 σC s c) := by
  have hin := wake_mainIn
  simp only [wakeMainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨hpro, h0⟩, hg1⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e1 : lab ".Lscc_rt_main.x2" = lab ".Lscc_rt_main.entry" + Int64.ofNat 9 := label_labelGapB hp hg1
  refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := wN0 lab J) (by decide) hF hR
    (by show R.lo ≤ -8 - (32 : Int64).toInt; rw [show (32 : Int64).toInt = 32 from rfl]; omega) hhi (by decide) rfl
    (by show SO.le ⟨-40, [(.rbp, -8)]⟩ (oF 32) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (wNC lab J))
      (seg_oneW (seg_ndW (by simp [wB0]) wB0_ok hF hR (by show R.lo ≤ -48; omega) hhi
        (code_field hp hend h0 (ofNat_zero' _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_)
  · -- the prologue
    intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨⟨σ, hJ, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩⟩
    · rw [hs]; simp [xStSlots, xS1, upd_apply]
    · rw [hs]; simp [xStSlots, xS1, upd_apply]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64]
    · rw [hr]; simp only [xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
      rw [show (32 : Int64).toBitVec = 32#64 from rfl, show BitVec.ofInt 64 (-8 - -40) = 32#64 from rfl]; bv_omega
  · simp only [wN0, wNC]; rw [wB0_run]
  · simp only [wN0, wNC]; rw [wB0_run]; simp [SO.le]
  · simp only [wN0, wNC] at hJ ⊢
    rw [wB0_run]
    obtain ⟨⟨σe, hJe, h1, h2, h3, h4, h5⟩, hb⟩ := hJ
    refine ⟨⟨σe, hJe, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [upd_apply, h1]
    · simp [upd_apply, h2]
    · simp [upd_apply, h3]
    · simp only [Reg64s.set64]; simp [h4]
    · simp [Reg64s.set64, h5]
    · simp [Reg64s.set64, upd_apply]
    · simp only [upd_apply, ↓reduceIte]
      rw [show lab ".Lscc_rt_main.x2" = _ from e1]; rfl
    · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; simp at hb ⊢; rw [hb]; bv_omega
  · -- `wc_main` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (wR R D) (wF R D F G.1 G.2)
      ⟨lab "wc_main", ⟨0, []⟩, wJ0 (wNC lab J).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR', hF'⟩ := wR_ok hD hD8 hR hF hlo hhi G.1 G.2
      exact (hWc G.1 G.2 hR' hF').mono_post fun s c h => ⟨G.1, G.2, h⟩
    · intro s c h
      obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD', hc, hσ, hJ⟩ := at_enter (e0 := 0) (lo' := -D) (hi' := 8)
        (by show R.lo ≤ -48 - 0 + -D; omega) (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega)
        (by show ((-48 : Int) - 0) % 8 = 0; decide) h
      exact ⟨(m0, σC), he, hn, hdc, hpc, σ, hA, hD', hσ, hc ▸ hJ⟩

end MainPre

end Spike.Lib.X64.Flow.WakeM

/-- info: 'Spike.Lib.X64.Flow.WakeM.wake_mainIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeM.wake_mainIn

/-- info: 'Spike.Lib.X64.Flow.WakeM.MainPreWW.triv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeM.MainPreWW.triv

/-- info: 'Spike.Lib.X64.Flow.WakeM.wR_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeM.wR_ok

/-- info: 'Spike.Lib.X64.Flow.WakeM.wake_main_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeM.wake_main_pre_segW
