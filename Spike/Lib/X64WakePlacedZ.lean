/-
**wake.w's worker environment placed, x86-64** (in the manner of
`Spike/Lib/A64WakePlacedZ.lean`): `Placed` (`Spike/Lib/X64Consumer.lean`)
holds at every node's states of the spawned child's run (`ThrZA`, and
`NodeZA` at the stub). It is `wakeZX`'s `Placed` conjunct.

The worker's argument pair `a` has two words: `w1` (the flag's address `A`)
and `w2` (the waiter's tid `B`). After the `split`, `c` is `w1` and `j` is
`w2`. They live where the code keeps `A` and `B`:
- `%r12`/`%rbx` in the stub;
- `%rdi`/`%rsi` at the calls' entries and through the prologues, which write
  neither;
- the frames' cells after the spills: `-16`/`-24` of `scc_rt_thr_worker`'s
  and `wc_worker`'s frames, and `j`'s at `-16` of `scc_rt_unpark`'s.
Past the `store` the control reads only `j` (`B`); past the `unpark` it
reads nothing.

- `envW`, `envJ`; `placed_ab`, `placed_j`, `placed_nil`: an environment
  placed by its free variables' places.
- `placed_kid`, `placed_wc1`, `placed_c2`, `placed_c3`: the worker's four
  controls.
- `xProW_rr`: a prologue's states placed from its entry's `%rdi`, `%rsi`.
- `unpk_placed`, `wk_placed`, `tail_placed`, `head_placed`: per function.
- `thrZA_placed`: `ThrZA Placed` of the thread worker; `cZA_placed`: at
  the child's stub.

**Unlike AArch64** (forced by the x64 shape):
- The argument registers are `%rdi`/`%rsi` (AArch64 `x0`/`x1`) and the
  stub's are `%r12`/`%rbx` (AArch64 `x9`/`x10`).
- The frames' cells are `-16`/`-24` below the region's base (AArch64
  `-48`/`-40` and `-32`/`-24`), and `j`'s in `scc_rt_unpark` is at `-16`
  (AArch64 `-48`).
- The prologue is an `XProW` of five nodes (`xProW_rr`; AArch64 `proW_x01`
  over `ProW`'s four).
- The block prefixes' "keep" facts are concrete `arun` evaluations per
  block (`MainW`'s style), instead of AArch64's `keep_blk`.
-/
import Spike.Lib.X64WakeMainW
import Spike.Lib.X64WakeRelZ

namespace Spike.Lib.X64.Flow.Worker.Wake.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Place WordPlace placeVal ValRep exprFv opVars opAts atVars)
open Spike.Lib (Region)
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZA thrJ thrJE wcJE)
open Spike.Lib.X64.WakePh.Child (cN childN childJ oC chB tsB jeB xbp)
open Spike.Lib.X64.Flow.Worker.Wake.Child (cBlk)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerRest workerTy wc1)
open Spike.Lib.X64WakeMainW (M1 placeVal_cell)
open Spike.Lib.X64Consumer (Placed)

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {s : State}

/-! ## Environments placed -/

/-- **The worker's words placed**: `a`'s at `pA`, `pB`, `c`'s at `pA`,
`j`'s at `pB`. -/
def envW (pA pB : Place M1.I.RegId) : String → Nat → Option (WordPlace M1.I.RegId) :=
  fun x k => if x = "a" ∧ k = 0 then some (.one pA) else if x = "a" ∧ k = 1 then some (.one pB)
    else if x = "c" ∧ k = 0 then some (.one pA) else if x = "j" ∧ k = 0 then some (.one pB) else none

/-- **`j`'s word placed** at `pB`. -/
def envJ (pB : Place M1.I.RegId) : String → Nat → Option (WordPlace M1.I.RegId) :=
  fun x k => if x = "j" ∧ k = 0 then some (.one pB) else none

/-- **A control reading only `a`, `c`, `j` is placed** by `envW`: `a`
bound to `[w1, w2]`, `c` to `[w1]`, `j` to `[w2]` (where bound), the
words' values at `pA`, `pB`. -/
theorem placed_ab {c : Ctl} {w1 w2 : TermRun.Word} {a b : Nat} {pA pB : Place M1.I.RegId}
    (ha : ∀ ty ws, TermRun.lookupE c.env "a" = some (ty, ws) → ws = [w1, w2])
    (hc : ∀ ty ws, TermRun.lookupE c.env "c" = some (ty, ws) → ws = [w1])
    (hj : ∀ ty ws, TermRun.lookupE c.env "j" = some (ty, ws) → ws = [w2])
    (hfv : ∀ y ∈ exprFv c.term, y = "a" ∨ y = "c" ∨ y = "j")
    (hpA : placeVal M1 s pA = some a) (hpB : placeVal M1 s pB = some b)
    (hv1 : ValRep lbl w1.val a) (hv2 : ValRep lbl w2.val b) : Placed Λ lbl s c := by
  refine ⟨envW pA pB, ?_, ?_, ?_⟩
  · intro y t ws hy k wd wp hwd hwp
    simp only [envW] at hwp
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = "a" ∧ k = 0›
      cases hwp; obtain rfl := ha _ _ hy; cases hwd; exact ⟨a, hpA, hv1⟩
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = "a" ∧ k = 1›
      cases hwp; obtain rfl := ha _ _ hy; cases hwd; exact ⟨b, hpB, hv2⟩
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = "c" ∧ k = 0›
      cases hwp; obtain rfl := hc _ _ hy; cases hwd; exact ⟨a, hpA, hv1⟩
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = "j" ∧ k = 0›
      cases hwp; obtain rfl := hj _ _ hy; cases hwd; exact ⟨b, hpB, hv2⟩
    cases hwp
  · intro y hy t ws hl k hk
    rcases hfv y hy with rfl | rfl | rfl
    · obtain rfl := ha _ _ hl
      rcases k with _ | _ | k
      · exact ⟨.one pA, by simp [envW]⟩
      · exact ⟨.one pB, by simp [envW]⟩
      · simp at hk; omega
    · obtain rfl := hc _ _ hl
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨.one pA, by simp [envW]⟩
    · obtain rfl := hj _ _ hl
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨.one pB, by simp [envW]⟩
  · intro y k n h
    simp only [envW] at h
    repeat' split at h
    all_goals cases h

/-- **A control reading only `j` is placed** by `envJ`: `j` bound to
`[w2]`, the word's value at `pB`. -/
theorem placed_j {c : Ctl} {w2 : TermRun.Word} {b : Nat} {pB : Place M1.I.RegId}
    (hj : ∀ ty ws, TermRun.lookupE c.env "j" = some (ty, ws) → ws = [w2])
    (hfv : ∀ y ∈ exprFv c.term, y = "j") (hpB : placeVal M1 s pB = some b) (hv2 : ValRep lbl w2.val b) :
    Placed Λ lbl s c := by
  refine ⟨envJ pB, ?_, ?_, ?_⟩
  · intro y t ws hy k wd wp hwd hwp
    simp only [envJ] at hwp
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = "j" ∧ k = 0›
      cases hwp; obtain rfl := hj _ _ hy; cases hwd; exact ⟨b, hpB, hv2⟩
    cases hwp
  · intro y hy t ws hl k hk
    obtain rfl := hfv y hy
    obtain rfl := hj _ _ hl
    obtain rfl : k = 0 := by simpa using hk
    exact ⟨.one pB, by simp [envJ]⟩
  · intro y k n h
    simp only [envJ] at h
    split at h <;> cases h

/-- **A control reading no variable is placed** (by the empty map). -/
theorem placed_nil {c : Ctl} (hfv : exprFv c.term = []) : Placed Λ lbl s c := by
  refine ⟨fun _ _ => none, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h; cases h
  · intro _ hy; simp [hfv] at hy
  · intro _ _ _ h; cases h

/-! ## The worker's controls -/

/-- The control past the `store` (`c2`). -/
abbrev c2W (w1 w2 : TermRun.Word) : Ctl :=
  ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩

/-- The control past the `unpark` (`c3`). -/
abbrev c3W (w1 w2 : TermRun.Word) : Ctl :=
  ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩

variable {w1 w2 : TermRun.Word} {a b : Nat} {pA pB : Place M1.I.RegId}

theorem placed_kid (T : Ty) (hpA : placeVal M1 s pA = some a) (hpB : placeVal M1 s pB = some b)
    (hv1 : ValRep lbl w1.val a) (hv2 : ValRep lbl w2.val b) :
    Placed Λ lbl s (Spike.Lib.X64.Flow.Worker.Wake.Child.kidC T w1 w2) :=
  placed_ab (fun _ _ h => by simp [Spike.Lib.X64.Flow.Worker.Wake.Child.kidC, TermRun.lookupE] at h; exact h.2.symm)
    (fun _ _ h => by simp [Spike.Lib.X64.Flow.Worker.Wake.Child.kidC, TermRun.lookupE] at h)
    (fun _ _ h => by simp [Spike.Lib.X64.Flow.Worker.Wake.Child.kidC, TermRun.lookupE] at h)
    (by simp [Spike.Lib.X64.Flow.Worker.Wake.Child.kidC, exprFv, atVars]) hpA hpB hv1 hv2

theorem placed_wc1 (hpA : placeVal M1 s pA = some a) (hpB : placeVal M1 s pB = some b)
    (hv1 : ValRep lbl w1.val a) (hv2 : ValRep lbl w2.val b) : Placed Λ lbl s (wc1 workerTy w1 w2) :=
  placed_ab (fun _ _ h => by simp [wc1, TermRun.lookupE] at h; exact h.2.symm)
    (fun _ _ h => by simp [wc1, TermRun.lookupE] at h; exact h.2.symm)
    (fun _ _ h => by simp [wc1, TermRun.lookupE] at h; exact h.2.symm)
    (by simp [wc1, workerRest, exprFv, opVars, opAts, atVars]) hpA hpB hv1 hv2

theorem placed_c2 (hpB : placeVal M1 s pB = some b) (hv2 : ValRep lbl w2.val b) : Placed Λ lbl s (c2W w1 w2) :=
  placed_j (fun _ _ h => by simp [wc1, TermRun.lookupE] at h; exact h.2.symm)
    (by simp [exprFv, opVars, opAts, atVars]) hpB hv2

theorem placed_c3 : Placed Λ lbl s (c3W w1 w2) :=
  placed_nil (by simp [exprFv, atVars])

/-! ## Blocks' prefixes -/

open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xSt xS1 xS2 xS3 hdRegs)

/-- The abstract run's simp set over concrete blocks (as in
`X64WakeMainW`). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

/-- **The prologue's prefixes keep `%rdi` and `%rsi`.** -/
theorem pro_rr (l : String → Int64) (pc : Int64) (o : SO) (σ : AS) (Z : Int64) (L : String)
    {blk : List (Directive × Nat)}
    (hb : blk = xHead ∨ blk = xLea Z 5 ∨ blk = xCmp L 3 2 ∨ blk = xFr Z 4 [(.rdi, -8, 4), (.rsi, -16, 4)])
    {k : Nat} (hk : k < blk.length) :
    (arun l (blk.take k) ⟨pc, o, σ⟩).σ.regs.get64 .rdi = σ.regs.get64 .rdi ∧
      (arun l (blk.take k) ⟨pc, o, σ⟩).σ.regs.get64 .rsi = σ.regs.get64 .rsi := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [xHead, xLea, xCmp, xFr, xSt, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases k with _|_|_|k <;> (try omega) <;> arun_simp

theorem xS1_rr (σ : AS) :
    (xS1 σ).regs.get64 .rdi = σ.regs.get64 .rdi ∧ (xS1 σ).regs.get64 .rsi = σ.regs.get64 .rsi := by
  simp only [xS1, hdRegs]
  constructor <;>
    rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide)]

theorem xS2_rr (Z : Int64) (σ : AS) :
    (xS2 Z σ).regs.get64 .rdi = σ.regs.get64 .rdi ∧ (xS2 Z σ).regs.get64 .rsi = σ.regs.get64 .rsi := by
  simp only [xS2]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide)]
  exact xS1_rr σ

theorem xS3_rr (Z : Int64) (v : BitVec 64) (σ : AS) :
    (xS3 Z v σ).regs.get64 .rdi = σ.regs.get64 .rdi ∧ (xS3 Z v σ).regs.get64 .rsi = σ.regs.get64 .rsi := by
  simp only [xS3, Spike.Lib.X64.fsStep]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide)]
  exact xS2_rr Z σ

/-- **`scc_rt_thr_worker`'s `.entry` prefixes keep the cells** (two loads
before the call). -/
theorem thE_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < ThrHeadW.thE.length) :
    (arun l (ThrHeadW.thE.take k) ⟨pc, ThrHeadW.oI, σ⟩).σ.slot = σ.slot := by
  simp only [ThrHeadW.thE] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> arun_simp

/-- **`wc_worker`'s `.entry` prefixes keep the cells** (loads). -/
theorem wkB0_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < WkTailW.b0.length) :
    (arun l (WkTailW.b0.take k) ⟨pc, WkTailW.oI, σ⟩).σ.slot = σ.slot := by
  simp only [WkTailW.b0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|k <;> (try omega) <;> arun_simp

/-- **`wc_worker`'s unpark-call prefixes keep the cells.** -/
theorem wkB1_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < WkTailW.b1.length) :
    (arun l (WkTailW.b1.take k) ⟨pc, WkTailW.oI, σ⟩).σ.slot = σ.slot := by
  simp only [WkTailW.b1] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|k <;> (try omega) <;> arun_simp

/-- **`scc_rt_unpark`'s prologue prefixes keep `%rdi`.** -/
theorem unB0_rdi (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < Unpark.b0.length) :
    (arun l (Unpark.b0.take k) ⟨pc, Unpark.oE, σ⟩).σ.regs.get64 .rdi = σ.regs.get64 .rdi := by
  simp only [Unpark.b0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp

/-- **`scc_rt_unpark`'s `.entry` prefixes keep the cells** (loads). -/
theorem unB1_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < Unpark.b1.length) :
    (arun l (Unpark.b1.take k) ⟨pc, Unpark.oI, σ⟩).σ.slot = σ.slot := by
  simp only [Unpark.b1] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|k <;> (try omega) <;> arun_simp

/-- **The stub's call prefixes keep `%r12` and `%rbx`.** -/
theorem chB_keep (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < chB.length) :
    (arun l (chB.take k) ⟨pc, oC, σ⟩).σ.regs.get64 .r12 = σ.regs.get64 .r12 ∧
      (arun l (chB.take k) ⟨pc, oC, σ⟩).σ.regs.get64 .rbx = σ.regs.get64 .rbx := by
  simp only [chB] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> arun_simp

/-! ## A prologue's states -/

section Pro

/-- **A prologue's states inside `W`** from its entry's: every control of
the entry invariant `J` in `W` at every state agreeing with the entry's on
`%rdi`, `%rsi` (`hW`); the prologue writes neither. -/
theorem xProW_rr {W : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {J : AS → Ctl → Prop}
    (hW : ∀ σ c, J σ c → ∀ s : State, s.st.1.regs.get64 .rdi = σ.regs.get64 .rdi →
      s.st.1.regs.get64 .rsi = σ.regs.get64 .rsi → W s c) :
    XProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L 5 9 3 2 4 [(.rdi, -8, 4), (.rsi, -16, 4)] J := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    have h := pro_rr (_root_.Executable.labels exe).label pc0 ⟨0, []⟩ σ Z L (.inl rfl) hk
    refine ⟨hW σ c hJ _ ?_ ?_, fun _ h => h⟩
    · show m.regs.get64 _ = _; rw [hA'.regs, h.1]
    · show m.regs.get64 _ = _; rw [hA'.regs, h.2]
  · rintro s σ1 c _ _ _ _ _ _ ⟨σ, hJ, rfl⟩ k hk m hA' _
    have h := pro_rr (_root_.Executable.labels exe).label (xProN1 pc0 J).pc (xProN1 pc0 J).o (xS1 σ) Z L (.inr (.inl rfl)) hk
    refine ⟨hW σ c hJ _ ?_ ?_, fun _ h => h⟩
    · show m.regs.get64 _ = _; rw [hA'.regs, h.1, (xS1_rr σ).1]
    · show m.regs.get64 _ = _; rw [hA'.regs, h.2, (xS1_rr σ).2]
  · rintro s c ⟨-, -, -, -, σ2, hA, -, σ, hJ, rfl⟩
    refine ⟨hW σ c hJ _ ?_ ?_, fun _ h => h⟩
    · rw [hA.regs, (xS2_rr Z σ).1]
    · rw [hA.regs, (xS2_rr Z σ).2]
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k hk m hA' _
    have h := pro_rr (_root_.Executable.labels exe).label (xProN3 ms pc0 5 9 Z lim J).pc (xProN3 ms pc0 5 9 Z lim J).o
      (xS3 Z (v.setWidth 64) σ) Z L
      (.inr (.inr (.inl rfl))) hk
    refine ⟨hW σ c hJ _ ?_ ?_, fun _ h => h⟩
    · show m.regs.get64 _ = _; rw [hA'.regs, h.1, (xS3_rr Z _ σ).1]
    · show m.regs.get64 _ = _; rw [hA'.regs, h.2, (xS3_rr Z _ σ).2]
  · rintro s σ4 c _ _ _ _ _ _ ⟨σ, v, hJ, -, hreg, -⟩ k hk m hA' _
    have h := pro_rr (_root_.Executable.labels exe).label (xProN4 ms pc0 5 9 3 2 Z lim J).pc
      (xProN4 ms pc0 5 9 3 2 Z lim J).o σ4 Z L (.inr (.inr (.inr rfl))) hk
    refine ⟨hW σ c hJ _ ?_ ?_, fun _ h => h⟩
    · show m.regs.get64 _ = _
      rw [hA'.regs, h.1, show σ4.regs.get64 .rdi = _ from congrArg (·.get64 .rdi) hreg, (xS3_rr Z _ σ).1]
    · show m.regs.get64 _ = _
      rw [hA'.regs, h.2, show σ4.regs.get64 .rsi = _ from congrArg (·.get64 .rsi) hreg, (xS3_rr Z _ σ).2]

end Pro

/-! ## Per function -/

section Nodes

open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake

variable {exe : _root_.Executable} {endPc : Int64} {A B : BitVec 64}

/-- **`Placed` at `scc_rt_unpark`'s nodes** (from `wc_worker`'s call, the
source at `c2`, then `c3`): `j`'s word `B` in `%rdi` at entry, in the cell
at `-16` after the spill. -/
theorem unpk_placed {R : Region} {F : MachineData → Prop} (hlo : R.lo ≤ -16) (hhi : -8 ≤ R.hi)
    {rbp1 ra1 tp : BitVec 64} (hv2 : ValRep lbl w2.val B.toNat) (i : Unpark.PN) :
    NodeZA (Placed Λ lbl) exe endPc R F
      (Unpark.N (_root_.Executable.labels exe).label (c2W w1 w2) (c3W w1 w2) B rbp1 ra1 tp i) (Unpark.blkN i) := by
  have hR : R.Off (-16) := ⟨by decide, hlo, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, h0, -⟩ := hJ
    refine ⟨placed_c2 (pB := .reg (.r .rdi)) ?_ hv2, fun _ h => h⟩
    show some (m.regs.get64 .rdi).toNat = _
    erw [hA'.regs, unB0_rdi _ _ _ hk, h0]
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, -, -, h16, -⟩ := hJ
    refine ⟨placed_c2 (pB := .slot (R.addr (-16)).toNat) ?_ hv2, fun _ h => h⟩
    erw [placeVal_cell hA' hR _ rfl, unB1_slot _ _ _ hk, h16]
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨⟨rfl, -, -, h16, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [Unpark.blkN] using hk
    refine ⟨placed_c2 (pB := .slot (R.addr (-16)).toNat) ?_ hv2, fun _ h => h⟩
    rw [placeVal_cell hA' hR _ rfl]; exact congrArg _ (congrArg _ h16)
  all_goals
    intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    first | obtain ⟨rfl, -⟩ := hJ | obtain ⟨⟨rfl, -⟩, -⟩ := hJ
    exact ⟨placed_c3, fun _ h => h⟩

/-- **`Placed` at `wc_worker`'s nodes** (the source at `wc1`, `c2`, `c3`):
`c`'s and `j`'s words in the cells at `-16`, `-24`. -/
theorem wk_placed {R : Region} {F : MachineData → Prop} (hlo : R.lo ≤ -24) (hhi : -8 ≤ R.hi)
    {rbp0 ra tp sp : BitVec 64} (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat)
    (i : WkTailW.PN) :
    NodeZA (Placed Λ lbl) exe endPc R F (WkTailW.NA (_root_.Executable.labels exe).label
      (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2) A B rbp0 ra tp sp i) (WkTailW.blkN i) := by
  have hR16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have hR24 : R.Off (-24) := ⟨by decide, by omega, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, -, -, h16, h24, -⟩ := hJ
    refine ⟨placed_wc1 (pA := .slot (R.addr (-16)).toNat) (pB := .slot (R.addr (-24)).toNat) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · erw [placeVal_cell hA' hR16 _ rfl, wkB0_slot _ _ _ hk, h16]
    · erw [placeVal_cell hA' hR24 _ rfl, wkB0_slot _ _ _ hk, h24]
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨⟨rfl, -, -, h16, h24, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [WkTailW.blkN] using hk
    refine ⟨placed_wc1 (pA := .slot (R.addr (-16)).toNat) (pB := .slot (R.addr (-24)).toNat) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · rw [placeVal_cell hA' hR16 _ rfl]; exact congrArg _ (congrArg _ h16)
    · rw [placeVal_cell hA' hR24 _ rfl]; exact congrArg _ (congrArg _ h24)
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, -, -, -, h24, -⟩ := hJ
    refine ⟨placed_c2 (pB := .slot (R.addr (-24)).toNat) ?_ hv2, fun _ h => h⟩
    erw [placeVal_cell hA' hR24 _ rfl, wkB1_slot _ _ _ hk, h24]
  · exact fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp [WkTailW.blkN])
  · intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    obtain ⟨rfl, -⟩ := hJ
    exact ⟨placed_c3, fun _ h => h⟩

/-- **`Placed` at `scc_rt_thr_worker`'s tail** (the source at `c3`, reading
nothing). -/
theorem tail_placed {R : Region} {F : MachineData → Prop} {tp sp0 : BitVec 64} (i : ThrTailW.PN) :
    NodeZA (Placed Λ lbl) exe endPc R F
      (ThrTailW.NA (_root_.Executable.labels exe).label (c3W w1 w2) tp sp0 i) (ThrTailW.blkN i) := by
  cases i <;> intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _ <;>
    first | obtain ⟨rfl, -⟩ := hJ | obtain rfl := hJ
  all_goals exact ⟨placed_c3, fun _ h => h⟩

/-- **`Placed` at `scc_rt_thr_worker`'s head** (the source at the worker's
body `kidC`): `a`'s words `A`, `B` in the frame's cells at `-16`, `-24`
(the call node has no instruction). -/
theorem head_placed {R : Region} {F : MachineData → Prop} (hlo : R.lo ≤ -24) (hhi : -8 ≤ R.hi) {T : Ty}
    {tp sp0 : BitVec 64} (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat) (i : ThrHeadW.TN) :
    NodeZA (Placed Λ lbl) exe endPc R F (ThrHeadW.tN (_root_.Executable.labels exe).label
      (thrJ (Spike.Lib.X64.Flow.Worker.Wake.Child.kidC T w1 w2) A B tp sp0) (fun _ c => c = wc1 workerTy w1 w2) i)
      (ThrHeadW.blkN i) := by
  have hR16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have hR24 : R.Off (-24) := ⟨by decide, by omega, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, h16, h24, -⟩ := hJ
    refine ⟨placed_kid T (pA := .slot (R.addr (-16)).toNat) (pB := .slot (R.addr (-24)).toNat) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · erw [placeVal_cell hA' hR16 _ rfl, thE_slot _ _ _ hk, h16]
    · erw [placeVal_cell hA' hR24 _ rfl, thE_slot _ _ _ hk, h24]
  · exact fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp [ThrHeadW.blkN])

/-- **`Placed` at every node's states of the thread worker's run**, the
source at the worker's body `kidC T w1 w2`, then `wc1`, `c2`, `c3`; `A`,
`B` the words `w1`, `w2`'s values. -/
theorem thrZA_placed {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hlo : R.lo ≤ -24)
    (hhi : -8 ≤ R.hi) {T : Ty} {tp sp0 : BitVec 64} (hv1 : ValRep lbl w1.val A.toNat)
    (hv2 : ValRep lbl w2.val B.toNat) :
    ThrZA (Placed Λ lbl) exe endPc R F ms (Spike.Lib.X64.Flow.Worker.Wake.Child.kidC T w1 w2)
      (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2) A B tp sp0 where
  pro := xProW_rr fun σ c hJ s h1 h2 => by
    obtain ⟨rfl, hdi, hsi, -⟩ := hJ
    refine placed_kid T (pA := .reg (.r .rdi)) (pB := .reg (.r .rsi)) ?_ ?_ hv1 hv2
    · show some (s.st.1.regs.get64 .rdi).toNat = _
      rw [h1]; exact congrArg _ (congrArg _ hdi)
    · show some (s.st.1.regs.get64 .rsi).toNat = _
      rw [h2]; exact congrArg _ (congrArg _ hsi)
  head := head_placed hlo hhi hv1 hv2
  wpro _ _ _ _ _ := xProW_rr fun σ c hJ s h1 h2 => by
    obtain ⟨⟨rfl, hdi, hsi, -⟩, -⟩ := hJ
    refine placed_wc1 (pA := .reg (.r .rdi)) (pB := .reg (.r .rsi)) ?_ ?_ hv1 hv2
    · show some (s.st.1.regs.get64 .rdi).toNat = _
      rw [h1]; exact congrArg _ (congrArg _ hdi)
    · show some (s.st.1.regs.get64 .rsi).toNat = _
      rw [h2]; exact congrArg _ (congrArg _ hsi)
  wk _ _ hC _ _ := wk_placed (by have := hC.lo; omega) (by have := hC.hi; omega) hv1 hv2
  unpk _ _ _ _ _ _ _ hC _ _ := unpk_placed (by have := hC.lo; omega) (by have := hC.hi; omega) hv2
  tail := tail_placed

/-- **`Placed` at the child's stub** (the source at the worker's body):
`a`'s words in `%r12`, `%rbx`. -/
theorem cZA_placed {R : Region} {F : MachineData → Prop} {T : Ty} {tp sp0 : BitVec 64}
    (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat) :
    ∀ i, NodeZA (Placed Λ lbl) exe endPc R F
      (cN (_root_.Executable.labels exe).label (Spike.Lib.X64.Flow.Worker.Wake.Child.kidC T w1 w2) A B tp sp0 i)
      (cBlk i) := by
  have one : ∀ {blk : List (Directive × Nat)}, blk.length = 1 → ∀ {k : Nat}, k < blk.length →
      ∀ (σ : AS) (c : Ctl) (pc : Int64) (m : MachineData),
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, oC, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, oC, σ⟩).σ →
      childJ (Spike.Lib.X64.Flow.Worker.Wake.Child.kidC T w1 w2) A B tp sp0 σ c → ∀ s' : State, s'.st.1 = m →
      Placed Λ lbl s' c := by
    intro blk hb k hk σ c pc m hA' hJ s' hs
    obtain rfl : k = 0 := by omega
    obtain ⟨rfl, h12, hbx, -⟩ := hJ
    refine placed_kid T (pA := .reg (.r .r12)) (pB := .reg (.r .rbx)) ?_ ?_ hv1 hv2
    · show some (s'.st.1.regs.get64 .r12).toNat = _
      rw [hs, hA'.regs]; exact congrArg _ (congrArg _ h12)
    · show some (s'.st.1.regs.get64 .rbx).toNat = _
      rw [hs, hA'.regs]; exact congrArg _ (congrArg _ hbx)
  intro i
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    exact ⟨one rfl hk σ c _ m hA' hJ.1 _ rfl, fun _ h => h⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    exact ⟨one rfl hk σ c _ m hA' hJ.1 _ rfl, fun _ h => h⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    exact ⟨one rfl hk σ c _ m hA' hJ _ rfl, fun _ h => h⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨⟨rfl, h12, hbx, -⟩, -⟩ := hJ
    have h := chB_keep (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label Spike.Lib.X64.WakePh.Child.chL + 2) σ hk
    refine ⟨placed_kid T (pA := .reg (.r .r12)) (pB := .reg (.r .rbx)) ?_ ?_ hv1 hv2, fun _ h => h⟩
    · show some (m.regs.get64 .r12).toNat = _
      rw [hA'.regs]; erw [h.1]; exact congrArg _ (congrArg _ h12)
    · show some (m.regs.get64 .rbx).toNat = _
      rw [hA'.regs]; erw [h.2]; exact congrArg _ (congrArg _ hbx)

end Nodes

end Spike.Lib.X64.Flow.Worker.Wake.PlacedZ

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.PlacedZ.thrZA_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.PlacedZ.thrZA_placed
