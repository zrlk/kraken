/-
**wake.w's worker environment placed** (AArch64): `Placed`
(`Spike/Lib/A64Consumer.lean`) at every node's states of the spawned
child's run (`ThrZA`, `NodeZA` at the stub), `wakeZX`'s `Placed` conjunct.
The worker's argument pair `a` (words `w1`, the flag's address `A`, and
`w2`, the waiter's tid `B`), and after the `split` `c` (`w1`) and `j`
(`w2`), live where the code keeps `A` and `B`: `x9`/`x10` in the stub,
`x0`/`x1` at the calls' entries and through the prologues (which write no
argument register), the frames' cells after the spills. Past the `store`
the control reads only `j` (`B`), past the `unpark` nothing. The listing is
wake.w's certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `envW`, `envJ`; `placed_ab`, `placed_j`, `placed_nil`: an environment
  placed by its free variables' places.
- `placed_kid`, `placed_wc1`, `placed_c2`, `placed_c3`: the worker's four
  controls.
- `proW_placed`: a prologue's states placed from its entry's argument
  registers.
- `unpk_placed`, `wk_placed`, `tail_placed`, `head_placed`: per function.
- `thrZA_placed`: `ThrZA Placed` of the thread worker; `cZA_placed`: at
  the child's stub.
-/
import Spike.Lib.A64WakeMainW
import Spike.Lib.A64WakeRelZ

namespace Spike.Lib.A64.Flow.Worker.Wake.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Place WordPlace placeVal ValRep exprFv opVars opAts atVars)
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZA thrJ thrJE wcJE)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN childN cBlk pfxM kidC childJ cb chB)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerRest workerTy wc1)
open Spike.Lib.A64WakeMainW (M1 placeVal_x placeVal_cell)
open Spike.Lib.A64Consumer (Placed)

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
    (hv1 : ValRep lbl w1.val a) (hv2 : ValRep lbl w2.val b) : Placed Λ lbl s (kidC T w1 w2) :=
  placed_ab (fun _ _ h => by simp [kidC, TermRun.lookupE] at h; exact h.2.symm)
    (fun _ _ h => by simp [kidC, TermRun.lookupE] at h) (fun _ _ h => by simp [kidC, TermRun.lookupE] at h)
    (by simp [kidC, exprFv, atVars]) hpA hpB hv1 hv2

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


/-! ## A prologue's states -/

section Pro

set_option linter.unusedSimpArgs false

variable {lab : Label → Int64}

/-- `x0`, `x1` kept by the stack check's head. -/
theorem keep_chkHead (Z : Int64) (r : XReg) (hr : r = .X0 ∨ r = .X1) :
    ∀ d ∈ chkHead Z, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  simp only [chkHead, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> rintro d (rfl | rfl) ⟨pc, o, σ⟩ <;> dstep_keep <;>
    simp [Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]

/-- `x0`, `x1` kept by the stack check's branch. -/
theorem keep_chkBr (L : Label) (r : XReg) (hr : r = .X0 ∨ r = .X1) :
    ∀ d ∈ chkBr L, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  simp only [chkBr, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> rintro d (rfl | rfl) ⟨pc, o, σ⟩ <;> dstep_keep <;>
    simp [Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]

/-- `x0`, `x1` kept by the frame's set-up and the parameters' stores. -/
theorem keep_frameSet (Z : Int64) (ps : List (XReg × Int64)) (r : XReg) (hr : r = .X0 ∨ r = .X1) :
    ∀ d ∈ frameSet Z ps, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  intro d hd am
  simp only [frameSet, List.mem_append, List.mem_map] at hd
  rcases hd with hd | ⟨q, -, rfl⟩
  · simp only [frSetup, List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain ⟨pc, o, σ⟩ := am
    rcases hd with rfl | rfl | rfl | rfl
    all_goals
      simp only [dstep, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.so,
      Spike.Lib.A64.Flow.AI.step, Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg, Spike.Lib.A64.Flow.regRes,
      spStr, Reg64s.getRegOrZr_X, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp,
      Reg64s.setRegOrSp64, ConstExpr.interp, Spike.Lib.A64.Flow.SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp,
      Reg64s.getRegOrSp64, RegOrSp.base, Spike.Lib.A64.Flow.SO.get, MachineData.setRegOrZr, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, Spike.Lib.A64.Flow.zrB, Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.kill,
      Spike.Lib.A64.Flow.SO.killZ, Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]
    all_goals rcases hr with rfl | rfl <;> rfl
  · obtain ⟨pc, o, σ⟩ := am
    rw [dstep_spStr]

theorem keep_chkRegs (Z : Int64) (rr : Reg64s) (r : XReg) (hr : r = .X0 ∨ r = .X1) :
    (chkRegs Z rr).getXReg r = rr.getXReg r := by
  rcases hr with rfl | rfl <;> rfl

theorem keep_ldStep (v : BitVec 64) (σ : AS) (r : XReg) (hr : r = .X0 ∨ r = .X1) :
    (ldStep .X10 v σ).regs.getXReg r = σ.regs.getXReg r := by
  rcases hr with rfl | rfl <;> rfl

/-- **A prologue's states inside `W`** from its entry's: every control of
the entry invariant `J` in `W` at every state agreeing with the entry's on
`x0`, `x1` (`hW`); the prologue writes neither (`chkRegs`, the limit's load
into `x10`, the check's branch, the frame's set-up). -/
theorem proW_x01 {W : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop}
    (hW : ∀ σ c, J σ c → ∀ s : State, (∀ r : XReg, r = .X0 ∨ r = .X1 → s.st.1.regs.getXReg r = σ.regs.getXReg r) →
      W s c) :
    ProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keep_chkHead Z r hr) k]
  · rintro s c ⟨-, -, -, -, σ1, hA, -, σ, hJ, rfl⟩
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact keep_chkRegs Z σ.regs r hr
  · rintro s σ2 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k _ m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keep_chkBr L r hr) k, keep_ldStep _ _ r hr]
    exact keep_chkRegs Z σ.regs r hr
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, he, -⟩ k _ m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keep_frameSet Z ps r hr) k, he, keep_ldStep _ _ r hr]
    exact keep_chkRegs Z σ.regs r hr

end Pro

/-! ## Per function -/

section Nodes

open Spike.Lib.A64.Flow (ND At BlkW NodeW arun dstep AM SO arun_take_reg arun_take_slot arun_take_slotO)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake

variable {exe : _root_.Executable} {endPc : Int64} {A B : BitVec 64}

/-- **`Placed` at `scc_rt_unpark`'s nodes** (from `wc_worker`'s call, the
source at `c2`, then `c3`): `j`'s word `B` in `x0` at entry, in the cell
at `-48` after the spill. -/
theorem unpk_placed {R : Region} {F : MachineData → Prop} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {x29 ra tp : BitVec 64} (hv2 : ValRep lbl w2.val B.toNat) (i : Unpark.PN) :
    NodeZA (Placed Λ lbl) exe endPc R F
      (Unpark.N (_root_.Executable.labels exe).label (c2W w1 w2) (c3W w1 w2) B x29 ra tp i) (Unpark.blkN i) := by
  have hR : R.Off (-48) := ⟨by decide, hlo, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨rfl, h0, -⟩ := hJ
    refine ⟨placed_c2 (pB := .reg (.x XReg.X0.idx)) ?_ hv2, fun _ h => h⟩
    rw [placeVal_x]; show some (m.regs.getXReg .X0).toBitVec.toNat = _
    rw [hA'.regs, arun_take_reg .X0 (by keep_blk [Unpark.blkN, Unpark.b0]) k]; exact congrArg _ (congrArg _ h0)
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨rfl, -, -, h48, -⟩ := hJ
    refine ⟨placed_c2 (pB := .slot (R.addr (-48)).toNat) ?_ hv2, fun _ h => h⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-48) (by keep_blk [Unpark.blkN, Unpark.b1]) k, h48]
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨⟨rfl, -, -, h48, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [Unpark.blkN] using hk
    refine ⟨placed_c2 (pB := .slot (R.addr (-48)).toNat) ?_ hv2, fun _ h => h⟩
    rw [placeVal_cell hA' hR _ rfl]; exact congrArg _ (congrArg _ h48)
  all_goals
    intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    first | obtain ⟨rfl, -⟩ := hJ | obtain ⟨⟨rfl, -⟩, -⟩ := hJ
    exact ⟨placed_c3, fun _ h => h⟩

/-- **`Placed` at `wc_worker`'s nodes** (the source at `wc1`, `c2`, `c3`):
`c`'s and `j`'s words in the cells at `-32`, `-24`. -/
theorem wk_placed {R : Region} {F : MachineData → Prop} (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {x29 ra tp : BitVec 64} (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat)
    (i : WkTailW.PN) :
    NodeZA (Placed Λ lbl) exe endPc R F (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label
      (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2) A B x29 ra tp i) (WkTailW.blkN i) := by
  have hR32 : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  have hR24 : R.Off (-24) := ⟨by decide, by omega, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨rfl, -, -, h32, h24, -⟩ := hJ
    refine ⟨placed_wc1 (pA := .slot (R.addr (-32)).toNat) (pB := .slot (R.addr (-24)).toNat) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · rw [placeVal_cell hA' hR32 _ rfl, arun_take_slot (-32) (by keep_blk [WkTailW.blkN, WkTailW.b0]) k, h32]
    · rw [placeVal_cell hA' hR24 _ rfl, arun_take_slot (-24) (by keep_blk [WkTailW.blkN, WkTailW.b0]) k, h24]
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨⟨rfl, -, -, h32, h24, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [WkTailW.blkN] using hk
    refine ⟨placed_wc1 (pA := .slot (R.addr (-32)).toNat) (pB := .slot (R.addr (-24)).toNat) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · rw [placeVal_cell hA' hR32 _ rfl]; exact congrArg _ (congrArg _ h32)
    · rw [placeVal_cell hA' hR24 _ rfl]; exact congrArg _ (congrArg _ h24)
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, -, -, -, h24, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [WkTailW.blkN, WkTailW.b1] using hk
    refine ⟨placed_c2 (pB := .slot (R.addr (-24)).toNat) ?_ hv2, fun _ h => h⟩
    rw [placeVal_cell hA' hR24 _ rfl]; exact congrArg _ (congrArg _ h24)
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨⟨rfl, -, -, -, h24, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [WkTailW.blkN, WkTailW.b2] using hk
    refine ⟨placed_c2 (pB := .slot (R.addr (-24)).toNat) ?_ hv2, fun _ h => h⟩
    rw [placeVal_cell hA' hR24 _ rfl]; exact congrArg _ (congrArg _ h24)
  · exact fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp [WkTailW.blkN])
  · intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    obtain ⟨rfl, -⟩ := hJ
    exact ⟨placed_c3, fun _ h => h⟩

/-- **`Placed` at `scc_rt_thr_worker`'s tail** (the source at `c3`, reading
nothing). -/
theorem tail_placed {R : Region} {F : MachineData → Prop} {tp : BitVec 64} (i : ThrTailW.PN) :
    NodeZA (Placed Λ lbl) exe endPc R F
      (ThrTailW.N ThrTailW.pfx0 (_root_.Executable.labels exe).label (c3W w1 w2) tp i) (ThrTailW.blkN i) := by
  cases i <;> intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _ <;>
    first | obtain ⟨rfl, -⟩ := hJ | obtain rfl := hJ
  all_goals exact ⟨placed_c3, fun _ h => h⟩

/-- **`Placed` at `scc_rt_thr_worker`'s head** (the source at the worker's
body `kidC`): `a`'s words `A`, `B` in the frame's cells at `-48`, `-40`
(the call node has no instruction). -/
theorem head_placed {R : Region} {F : MachineData → Prop} (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) {T : Ty}
    {tp sp0 : BitVec 64} (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat) (i : ThrHeadW.TN) :
    NodeZA (Placed Λ lbl) exe endPc R F (ThrHeadW.tN ThrTailW.pfx0 (_root_.Executable.labels exe).label
      (thrJ (kidC T w1 w2) A B tp sp0) (fun _ c => c = wc1 workerTy w1 w2) i) (ThrHeadW.blkN i) := by
  have hR48 : R.Off (-48) := ⟨by decide, by omega, by omega⟩
  have hR40 : R.Off (-40) := ⟨by decide, by omega, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨rfl, h48, h40, -⟩ := hJ
    refine ⟨placed_kid T (pA := .slot (R.addr (-48)).toNat) (pB := .slot (R.addr (-40)).toNat) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · rw [placeVal_cell hA' hR48 _ rfl, arun_take_slot (-48) (by keep_blk [ThrHeadW.blkN, ThrHeadW.thE]) k, h48]
    · rw [placeVal_cell hA' hR40 _ rfl, arun_take_slot (-40) (by keep_blk [ThrHeadW.blkN, ThrHeadW.thE]) k, h40]
  · exact fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp [ThrHeadW.blkN])

/-- **`Placed` at every node's states of the thread worker's run**, the
source at the worker's body `kidC T w1 w2`, then `wc1`, `c2`, `c3`; `A`,
`B` the words `w1`, `w2`'s values. -/
theorem thrZA_placed {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hlo : R.lo ≤ -128)
    (hhi : 0 ≤ R.hi) {T : Ty} {tp sp0 : BitVec 64} (hv1 : ValRep lbl w1.val A.toNat)
    (hv2 : ValRep lbl w2.val B.toNat) :
    ThrZA (Placed Λ lbl) exe endPc R F ms (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2) A B tp sp0 where
  pro := proW_x01 fun σ c hJ s hx => by
    obtain ⟨rfl, h0, h1, -⟩ := hJ
    refine placed_kid T (pA := .reg (.x XReg.X0.idx)) (pB := .reg (.x XReg.X1.idx)) ?_ ?_ hv1 hv2
    · rw [placeVal_x, hx .X0 (.inl rfl)]; exact congrArg _ (congrArg _ h0)
    · rw [placeVal_x, hx .X1 (.inr rfl)]; exact congrArg _ (congrArg _ h1)
  head := head_placed hlo hhi hv1 hv2
  wpro _ _ _ _ _ := proW_x01 fun σ c hJ s hx => by
    obtain ⟨⟨rfl, h0, h1, -⟩, -⟩ := hJ
    refine placed_wc1 (pA := .reg (.x XReg.X0.idx)) (pB := .reg (.x XReg.X1.idx)) ?_ ?_ hv1 hv2
    · rw [placeVal_x, hx .X0 (.inl rfl)]; exact congrArg _ (congrArg _ h0)
    · rw [placeVal_x, hx .X1 (.inr rfl)]; exact congrArg _ (congrArg _ h1)
  wk _ _ hC _ _ := wk_placed (Int.le_trans hC.lo (by decide)) hC.hi hv1 hv2
  unpk _ _ _ _ _ _ _ hC _ _ := unpk_placed hC.lo hC.hi hv2
  tail := tail_placed

/-- **`Placed` at the child's stub** (the source at the worker's body):
`a`'s words in `x9`, `x10`. -/
theorem cZA_placed {R : Region} {F : MachineData → Prop} {T : Ty} {tp sp0 : BitVec 64}
    (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat) :
    ∀ i, NodeZA (Placed Λ lbl) exe endPc R F (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i)
      (cBlk i) := by
  intro i
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, -, h9, h10, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [cBlk, cb] using hk
    refine ⟨placed_kid T (pA := .reg (.x XReg.X9.idx)) (pB := .reg (.x XReg.X10.idx)) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · rw [placeVal_x]; show some (m.regs.getXReg .X9).toBitVec.toNat = _
      rw [hA'.regs]; exact congrArg _ (congrArg _ h9)
    · rw [placeVal_x]; show some (m.regs.getXReg .X10).toBitVec.toNat = _
      rw [hA'.regs]; exact congrArg _ (congrArg _ h10)
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨_, rfl, -, h9, h10, -⟩ := hJ
    refine ⟨placed_kid T (pA := .reg (.x XReg.X9.idx)) (pB := .reg (.x XReg.X10.idx)) ?_ ?_ hv1 hv2,
      fun _ h => h⟩
    · rw [placeVal_x]; show some (m.regs.getXReg .X9).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X9 (by keep_blk [cBlk, chB]) k]; exact congrArg _ (congrArg _ h9)
    · rw [placeVal_x]; show some (m.regs.getXReg .X10).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X10 (by keep_blk [cBlk, chB]) k]; exact congrArg _ (congrArg _ h10)

end Nodes

end Spike.Lib.A64.Flow.Worker.Wake.PlacedZ
