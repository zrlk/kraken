/-
**wake.w's `scc_rt_main` up to `wc_main`'s entry** (AArch64, the
pre-spawn consumer): `wake_main_pre_segW`, the segment from
`scc_rt_main`'s entry through its stack-checked prologue (frame 48, `x0`
saved at the frame's base) and its `.0_entry` block (`ldr x0, [sp]`,
`bl wc_main`) into `wc_main` in its region at the call, followed by a
segment of `wc_main` there (`hWc`, the instance's: `wc_main` does not
return before the `clone`).

wake.w's `main` takes its `ThreadId` (`tidStartT`), so `scc_rt_main`'s
`.0_entry` reloads the saved `x0` before the call: not `mainUIn`'s
one-instruction block (`Spike/Lib/Rt/A64Main.lean`), hence this file.

- `wB0`, `wakeMainIn`, `wake_mainIn`: the block and the code check, decided
  on `wakeProg`;
- `wJ`, `wN0`, `wNC`, `wR`, `wF`, `wJ0`: `scc_rt_main`'s frame, its nodes,
  `wc_main`'s region (depth `D` below the frame), frame condition and entry
  invariant at the call;
- `MainPreWW`: `scc_rt_main`'s own states inside `W` (prologue, call block);
- `wake_main_pre_segW`: the segment.
-/
import Spike.Lib.Rt.A64Main
import Spike.Lib.A64WakeCode

namespace Spike.Lib.A64.Flow.WakeM

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (LimOk seg_oneW)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

/-! ## `scc_rt_main`'s call block -/

/-- `scc_rt_main`'s `.0_entry` block: the saved `x0` (main's `ThreadId`)
back, the call of `wc_main`. -/
def wB0 : List Directive := parseAArch64("ldr x0, [sp]
bl wc_main")

block_spec wB0 (-48) 0 (⟨-48, []⟩ : SO) wB0

/-- **`scc_rt_main`'s code in `prog`**: the stack-checked prologue (frame
48, the limit at `[tpidr_el0, #8]`, `x0` at the frame's base), `wB0` at
`.0_entry`, `.sp0` right after it. -/
def wakeMainIn (prog : List Directive) : Bool :=
  prologueIn prog "scc_rt_main" ".L1_scc_rt_main.stack_check" ".L1_scc_rt_main.0_entry" 48 8
      ".L1_scc_rt_main.stack_grow" [(.X0, 0)] &&
    blockAt prog ".L1_scc_rt_main.0_entry" 0 wB0 &&
    labelGap prog ".L1_scc_rt_main.0_entry" ".L1_scc_rt_main.sp0" 2

theorem wake_mainIn : wakeMainIn SccCode.wakeProg = true := by decide +kernel

/-! ## Nodes -/

/-- **`scc_rt_main`'s frame** as some entry state of `J` left it: the
record, the saved `x0`, `sp` 48 below, the thread pointer. -/
def wJ (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec ∧
    σ.slot (-48) = σe.regs.X0.toBitVec ∧ σ.regs.SP.toBitVec = σe.regs.SP.toBitVec - (48 : Int64).toBitVec ∧
    σ.regs.TPIDR_EL0 = σe.regs.TPIDR_EL0

section Nodes

variable (lab : Label → Int64) (J : AS → Ctl → Prop)

/-- `scc_rt_main`'s `.0_entry`. -/
def wN0 : ND := ⟨lab ".L1_scc_rt_main.0_entry", ⟨-48, []⟩, wJ J⟩

/-- The call of `wc_main`: `x0` the saved `ThreadId`, the return address
`.sp0`. -/
def wNC : ND := ⟨lab "wc_main", ⟨-48, []⟩, fun σ c => wJ J σ c ∧
  σ.regs.X0.toBitVec = σ.slot (-48) ∧ σ.regs.X30.toBitVec = (lab ".L1_scc_rt_main.sp0").toBitVec⟩

end Nodes

/-- `wc_main`'s region at the call, `D` deep. -/
abbrev wR (R : Region) (D : Int) : Region := R.callee (-48) (-D) 0

/-- **`wc_main`'s frame condition at the call** from the caller's state
`m0`, `σC` (`at_enter`). -/
def wF (R : Region) (D : Int) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-48) (-D) 0 m0 m ∧ Abs R ⟨-48, []⟩ m0 σC

/-- `wc_main`'s entry invariant from the caller's state `σC` at the call
node of invariant `Jc`. -/
def wJ0 (Jc : AS → Ctl → Prop) (σC : AS) (σ : AS) (c : Ctl) : Prop := σ = enter (-48) σC ∧ Jc σC c

/-- **`scc_rt_main`'s own states up to the call inside `W`**, none moved by
`K`: its prologue's and the call block's. -/
structure MainPreWW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 48 8
    ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J
  call : BlkW W K exe endPc R F (wN0 (_root_.Executable.labels exe).label J) wB0

/-- `scc_rt_main`'s own states up to the call are inside the trivial
predicate, with no outside moves. -/
theorem MainPreWW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J : AS → Ctl → Prop} :
    MainPreWW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J :=
  ⟨ProW.triv, BlkW.triv⟩

section MainPre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- `wc_main`'s region at the call is a region, 16-aligned, its frame
condition stable. -/
theorem wR_ok {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hF : FStable R F) (hlo : R.lo ≤ -48 - D) (hhi : 0 ≤ R.hi) (m0 : MachineData) (σC : AS) :
    (wR R D).OK ∧ (wR R D).base.toNat % 16 = 0 ∧ FStable (wR R D) (wF R D F m0 σC) := by
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -D by omega) (by omega)
    (show (-48 : Int) < R.hi by omega)
  refine ⟨Region.callee_ok hR (by omega) (by omega) (by omega) (by omega), ?_,
    fstable_enter hR hF (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  have : (((wR R D).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **`scc_rt_main` up to `wc_main`, then `wc_main`, is one segment inside
`W`** in any valid layout of `wakeProg`: from `scc_rt_main`'s entry
(invariant `J`, `sp` at the region's base) through its prologue (the limit
word's facts for its frame, `hlimM`) and the call into `wc_main`'s region
at the call (`D` deep), then `wc_main`'s segment there to `Q m0 σC` for
every caller's state at the call (`hWc`). `scc_rt_main`'s states lie in
`W`, none moved by `K` (`hW`). -/
theorem wake_main_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48 - D) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} (hW : MainPreWW W K exe endPc R F ms J)
    (hlimM : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (48 : Int64).toBitVec))
    {Q : MachineData → AS → Frag isaLSE2}
    (hWc : ∀ m0 σC, (wR R D).OK → (wR R D).base.toNat % 16 = 0 → FStable (wR R D) (wF R D F m0 σC) →
      SegW W K p lbl ms (At exe endPc (wR R D) (wF R D F m0 σC)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wJ0 (wNC (_root_.Executable.labels exe).label J).J σC⟩) (Q m0 σC)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => ∃ m0 σC, Q m0 σC s c) := by
  have hin := wake_mainIn
  simp only [wakeMainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨hpro, h0⟩, hg1⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e1 : lab ".L1_scc_rt_main.sp0" = lab ".L1_scc_rt_main.0_entry" + Int64.ofNat (4 * 2) :=
    label_labelGap hp hg1
  refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := wN0 lab J) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -48; omega) hhi (by simp [Spike.Lib.offOk]) rfl
    (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (wNC lab J))
      (seg_oneW (seg_ndW (by simp [wB0]) wB0_ok hF hR hal (by show R.lo ≤ -48; omega) hhi
        (code_of hp hend h0 (ofNat4_zero _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_)
  · -- the prologue
    intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Ret0.setXReg_TPIDR]
  · simp only [wN0, wNC]; rw [wB0_run]
  · simp only [wN0, wNC]; rw [wB0_run]; simp [SO.le]
  · simp only [wN0, wNC] at hJ ⊢
    rw [wB0_run]
    obtain ⟨σe, hJe, h1, h2, h3, h4, h5⟩ := hJ
    refine ⟨⟨σe, hJe, h1, h2, h3, h4, h5⟩, rfl, ?_⟩
    rw [e1]
    show BitVec.ofInt 64 _ = _
    rw [Ret0.ofInt_bmod]
    simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
    rfl
  · -- `wc_main` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (wR R D) (wF R D F G.1 G.2)
      ⟨lab "wc_main", ⟨0, []⟩, wJ0 (wNC lab J).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR', hal', hF'⟩ := wR_ok hD hD16 hR hal hF hlo hhi G.1 G.2
      exact (hWc G.1 G.2 hR' hal' hF').mono_post fun s c h => ⟨G.1, G.2, h⟩
    · intro s c h
      obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD', hc, hσ, hJ⟩ := at_enter (lo' := -D) (hi' := 0)
        (by show R.lo ≤ -48 + -D; omega) (by show (-48 : Int) < R.hi; omega) (by decide)
        (by show (-48 : Int) % 8 = 0; decide) h
      exact ⟨(m0, σC), he, hn, hdc, hpc, σ, hA, hD', hσ, hc ▸ hJ⟩

end MainPre

end Spike.Lib.A64.Flow.WakeM

/-- info: 'Spike.Lib.A64.Flow.WakeM.wake_mainIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeM.wake_mainIn

/-- info: 'Spike.Lib.A64.Flow.WakeM.wake_main_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeM.wake_main_pre_segW
