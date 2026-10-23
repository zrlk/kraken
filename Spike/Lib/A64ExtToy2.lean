/-
**A refused `write` aborts**: the second closed `Correct` on the canonical
AArch64 target (`canonical 1`), and the first use of `Correct`'s abort
clause. The text

    _start: movz x0, #2; movz x1, #0; movz x2, #0; movz x8, #64; svc #0
            add x9, x0, #4; cbz x9, ok; add x9, x0, #11; cbz x9, ok
            movz x0, #101; movz x8, #94
    scc_abort_4: svc #0
    ok:     movz x0, #42; movz x8, #94; svc #0

calls `write(2, 0, 0)`; on `-EINTR` or `-EAGAIN` it calls `exit_group(42)`;
on a refusal (`0` or another error, `Kernel.writeRefused`; the kernel model
emits `writeErr`) it calls `exit_group(101)` at `trivLayout`'s `writeErr`
abort label (`scc_abort_4`), which the kernel model ends as
`abort writeErr`. It is a correct lowering of `Spike.Lib.A64ExtToy.toyP`
(`main` returns `42`) under the same configuration as toy 1: the abort is
justified by the `writeErr` in the trace (`AbortJustified … .writeErr`).

The trust boundary is again the parse of the text: the two hypotheses of
`toy2_correct`, checked by evaluation (`#guard`, below).

The proof (`Scc.Sem.StepSim`, as toy 1):

- **Code states** (`Live n r m`): the thread is at directive `n` of the
  executable (`atI n m`), its registers as the code has set them, with the
  `write`'s result `r`; symbolic in the machine data, so that the kernel's
  every result is one state family. The refused branch (directives 10 to 13)
  has `writeRefused r`.
- **Steps** (`live_step`): instructions (`next`, by the `exec_*` rows); the
  `write` (`sys5`: `-EINTR`/`-EAGAIN` with no event, a refusal with
  `writeErr`); `exit_group(42)` (`exit 42`); at the abort site
  `exit_group(101)` only as `abort writeErr` (`Step.sys` forbids `exit`
  there). No promise is certifiable (`no_certOkC`: certification passes the
  `write` with each of its results, `ret_of_results`, and stops at the
  `exit_group`s), no spawn, no range transfer.
- **The abort clause**: the trace invariant `Inv` (in the refused branch the
  trace has `writeErr`) holds along every run (`inv_run`), so an abort step,
  taken at directive 13, follows a `writeErr`.
- **Progress** (`live_progress`): the `write` may return `-EINTR`, the abort
  site may abort; **components**: toy 1's (`Spike.Lib.A64ExtToy.components`).
-/
import Spike.Lib.A64ExtToy
import Spike.Bridge.CertC

namespace Spike.Lib.A64ExtToy2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Kraken.Promising.Lower
open Spike.Bridge.CertC (stepC_silent stepC_dead no_certOkC_of_closed)
open Spike.Lib.A64ExtToy (Λ T K0 mem0 get_one abi_atSys not_ready runs_pre inLayout_mem toyP toyCfg S s0 s1 src_step wit
  components)

/-! ## The text and its cells -/

/-- The text: `write(2, 0, 0)`; on a refusal, `exit_group(101)` at the
`writeErr` abort site; on `-EINTR` or `-EAGAIN`, `exit_group(42)`. -/
def toy2Asm : String :=
  "\t.text\n\t.globl _start\n_start:\n\tmovz x0, #2\n\tmovz x1, #0\n\tmovz x2, #0\n\tmovz x8, #64\n\tsvc #0\n" ++
  "\tadd x9, x0, #4\n\tcbz x9, ok\n\tadd x9, x0, #11\n\tcbz x9, ok\n\tmovz x0, #101\n\tmovz x8, #94\n" ++
  "scc_abort_4:\n\tsvc #0\nok:\n\tmovz x0, #42\n\tmovz x8, #94\n\tsvc #0\n"

/-- `movz r, #v`. -/
def mz (r : XReg) (v : Int64) : Directive := .instr ⟨.W64, .MOVZ (.low (.reg r) .W64) (.int64 v) .LSL0⟩

/-- `svc #0`. -/
def sv : Directive := .instr ⟨.W64, .SVC 0⟩

/-- `add x9, x0, #v`. -/
def ad (v : Int64) : Directive :=
  .instr ⟨.W64, .ADD_e (.low (.reg .X9) .W64) (.low (.reg .X0) .W64) (.imm ⟨.int64 v, .S0⟩)⟩

/-- `cbz x9, ok`. -/
def cz : Directive := .instr ⟨.W64, .CBZ (.low (.reg .X9) .W64) (.label "ok")⟩

/-- The parsed program of the text. -/
def toy2Prog : Program :=
  [.label "_start", mz .X0 2, mz .X1 0, mz .X2 0, mz .X8 64, sv, ad 4, cz, ad 11, cz, mz .X0 101, mz .X8 94,
    .label "scc_abort_4", sv, .label "ok", mz .X0 42, mz .X8 94, sv]

-- The trust boundary, checked by evaluation: the canonical loader's parse of
-- the text is `toy2Prog`, with no data section.
#guard (textProgram toy2Asm).toOption == some toy2Prog
#guard (dataSections toy2Asm).isEqSome {}

/-- The loaded thread state (`threadAt` at `Λ.code.lo`). -/
def st0 : State := threadAt Entry.linux Λ.code.lo toy2Prog []

/-- The loaded state at directive `n` of the executable, with machine data `m`. -/
def atI (n : Nat) (m : MachineData) : State := { st0 with st := (m, Kraken.Executable.addrOf st0.exe n) }

instance validLayout : Kraken.Executable.ValidLayout st0.exe := by
  constructor
  all_goals first
  | decide +kernel
  | (intro i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp_all [st0, threadAt, toy2Prog, placeSyms, placeBelow, symsBelow, exeStart, symsFrom, padTo, Directive.fakeSize, mz, sv, ad, cz])

theorem endPc_eq : st0.endPc = st0.exe.1 + .ofNat (st0.exe.2.map (·.2)).sum := by decide +kernel

theorem len_exe : st0.exe.2.length = 18 := by decide +kernel

/-- **Directive `n` is the 4-byte cell `d` at `atI n m`**, given the
directives from `n` on. -/
theorem cell {n : Nat} {d : Directive}
    (h : ((st0.exe.2.drop n).dropWhile (fun c => c.1.isLabel)).head? = some (d, 4)) (hn : n ≤ 18)
    (m : MachineData) : CellAt (atI n m) d 4 := by
  obtain ⟨rest, hr⟩ : ∃ rest, (st0.exe.2.drop n).dropWhile (fun c => c.1.isLabel) = (d, 4) :: rest := by
    revert h
    cases (st0.exe.2.drop n).dropWhile (fun c => c.1.isLabel) with
    | nil => intro h; cases h
    | cons x xs => intro h; cases h; exact ⟨xs, rfl⟩
  refine cellAt_of_codeAt (rest := rest) validLayout endPc_eq ?_
  show Kraken.Executable.codeAt st0.exe (Kraken.Executable.addrOf st0.exe n) = _
  rw [Kraken.Executable.codeAt_addrOf_drop st0.exe (len_exe ▸ hn)]; exact hr

/-- The address of directive `n`. -/
abbrev pcI (n : Nat) : Int64 := Kraken.Executable.addrOf st0.exe n

/-- `movz r, #v` on machine data. -/
def mzD (r : XReg) (v : Nat) (m : MachineData) : MachineData :=
  { m with regs := m.regs.setRegOrZr (.low (.reg r) .W64) (BitVec.ofNat 64 v) }

/-- `add x9, x0, #v` on machine data. -/
def adD (v : Int64) (m : MachineData) : MachineData :=
  { m with regs := m.regs.setRegOrSp (.low (.reg .X9) .W64) (m.regs.getRegOrSp (.low (.reg .X0) .W64) + v.toBitVec) }

/-- The directives from `n` on start with the 4-byte cell `d`. -/
abbrev HeadAt (n : Nat) (d : Directive) : Prop :=
  ((st0.exe.2.drop n).dropWhile (fun c => c.1.isLabel)).head? = some (d, 4)

theorem exec_mz {n n' : Nat} {r : XReg} {w : Int64} {v : Nat} (hd : HeadAt n (mz r w)) (hn : n ≤ 18)
    (hpc : Kraken.Executable.addrOf st0.exe n + .ofNat 4 = Kraken.Executable.addrOf st0.exe n')
    (hv : (BitVec.ofInt 64 w.toInt &&& 65535#64) <<< 0 = BitVec.ofNat 64 v)
    (m : MachineData) : isaLSE2.exec (atI n m) = some (.done (atI n' (mzD r v m))) := by
  rw [exec_movz (cell hd hn m)]
  simp only [after, atI, mzD, ConstExpr.interp]
  rw [← hv, ← hpc]

theorem exec_ad {n n' : Nat} {w : Int64} (hd : HeadAt n (ad w)) (hn : n ≤ 18)
    (hpc : Kraken.Executable.addrOf st0.exe n + .ofNat 4 = Kraken.Executable.addrOf st0.exe n') (m : MachineData) :
    isaLSE2.exec (atI n m) = some (.done (atI n' (adD w m))) := by
  rw [exec_add_e_imm (cell hd hn m)]
  simp only [after, atI, adD]
  rw [← hpc]

theorem br (n : Nat) (m : MachineData) : branchTarget (atI n m) 4 (.label "ok") = pcI 15 := by
  show (_root_.Executable.labels st0.exe).label "ok" = pcI 15
  rw [Kraken.Executable.label_addrOf st0.exe "ok" 14 (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem exec_cz {n n' : Nat} (hd : HeadAt n cz) (hn : n ≤ 18)
    (hpc : Kraken.Executable.addrOf st0.exe n + .ofNat 4 = Kraken.Executable.addrOf st0.exe n') (m : MachineData) :
    isaLSE2.exec (atI n m) =
      some (.done (if m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0 then atI 15 m else atI n' m)) := by
  rw [exec_cbz (cell hd hn m), br]
  show some (EvTree.done (jumpTo (atI n m) m (if m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0 then pcI 15
    else Kraken.Executable.addrOf st0.exe n + .ofNat 4))) = _
  by_cases h : m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, hpc]; rfl

theorem exec1 (m : MachineData) : isaLSE2.exec (atI 1 m) = some (.done (atI 2 (mzD .X0 2 m))) :=
  exec_mz (w := 2) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec2 (m : MachineData) : isaLSE2.exec (atI 2 m) = some (.done (atI 3 (mzD .X1 0 m))) :=
  exec_mz (w := 0) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec3 (m : MachineData) : isaLSE2.exec (atI 3 m) = some (.done (atI 4 (mzD .X2 0 m))) :=
  exec_mz (w := 0) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec4 (m : MachineData) : isaLSE2.exec (atI 4 m) = some (.done (atI 5 (mzD .X8 64 m))) :=
  exec_mz (w := 64) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec6 (m : MachineData) : isaLSE2.exec (atI 6 m) = some (.done (atI 7 (adD 4 m))) :=
  exec_ad (by decide +kernel) (by decide) (by decide +kernel) m

theorem exec7 (m : MachineData) : isaLSE2.exec (atI 7 m) =
    some (.done (if m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0 then atI 15 m else atI 8 m)) :=
  exec_cz (by decide +kernel) (by decide) (by decide +kernel) m

theorem exec8 (m : MachineData) : isaLSE2.exec (atI 8 m) = some (.done (atI 9 (adD 11 m))) :=
  exec_ad (by decide +kernel) (by decide) (by decide +kernel) m

theorem exec9 (m : MachineData) : isaLSE2.exec (atI 9 m) =
    some (.done (if m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0 then atI 15 m else atI 10 m)) :=
  exec_cz (by decide +kernel) (by decide) (by decide +kernel) m

theorem exec10 (m : MachineData) : isaLSE2.exec (atI 10 m) = some (.done (atI 11 (mzD .X0 101 m))) :=
  exec_mz (w := 101) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec11 (m : MachineData) : isaLSE2.exec (atI 11 m) = some (.done (atI 13 (mzD .X8 94 m))) :=
  exec_mz (w := 94) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec15 (m : MachineData) : isaLSE2.exec (atI 15 m) = some (.done (atI 16 (mzD .X0 42 m))) :=
  exec_mz (w := 42) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

theorem exec16 (m : MachineData) : isaLSE2.exec (atI 16 m) = some (.done (atI 17 (mzD .X8 94 m))) :=
  exec_mz (w := 94) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) m

/-- The `svc` cells. -/
theorem cellSv {n : Nat} (hd : HeadAt n sv) (hn : n ≤ 18 := by decide) (m : MachineData) :
    CellAt (atI n m) sv 4 := cell hd hn m

/-! ## The code states -/

/-- What the registers hold at each directive (the write returned `r`). -/
macro "rsimp" : tactic => `(tactic| simp [mzD, adD, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg,
  Reg64s.getRegOrZr, Reg64s.getRegOrZr64, Reg64s.getXReg, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
  Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrZr.base, RegOrSp.base])

/-- A possible result of the `write`: `-EINTR`, `-EAGAIN` or a refusal. -/
def Ret (r : BitVec 64) : Prop :=
  r = Kernel.neg Kernel.eintr ∨ r = Kernel.neg Kernel.eagain ∨ Kernel.writeRefused r = true

/-- **The code states**: the thread is at directive `n` with machine data
`m`, the `write` having returned `r` (if it has). -/
def Live : Nat → BitVec 64 → MachineData → Prop
  | 1, _, _ => True
  | 2, _, m => m.regs.X0 = 2
  | 3, _, m => m.regs.X0 = 2 ∧ m.regs.X1 = 0
  | 4, _, m => m.regs.X0 = 2 ∧ m.regs.X1 = 0 ∧ m.regs.X2 = 0
  | 5, _, m => m.regs.X0 = 2 ∧ m.regs.X1 = 0 ∧ m.regs.X2 = 0 ∧ m.regs.X8 = 64
  | 6, r, m => m.regs.X0.toBitVec = r ∧ Ret r
  | 7, r, m => m.regs.X0.toBitVec = r ∧ m.regs.X9.toBitVec = r + 4 ∧ Ret r
  | 8, r, m => m.regs.X0.toBitVec = r ∧ Ret r ∧ r + 4 ≠ 0
  | 9, r, m => m.regs.X9.toBitVec = r + 11 ∧ Ret r ∧ r + 4 ≠ 0
  | 10, r, _ => Kernel.writeRefused r = true
  | 11, r, m => Kernel.writeRefused r = true ∧ m.regs.X0 = 101
  | 13, r, m => Kernel.writeRefused r = true ∧ m.regs.X0 = 101 ∧ m.regs.X8 = 94
  | 15, _, _ => True
  | 16, _, m => m.regs.X0 = 42
  | 17, _, m => m.regs.X0 = 42 ∧ m.regs.X8 = 94
  | _, _, _ => False

/-- Past both `cbz`, the result is a refusal. -/
theorem refused_of {r : BitVec 64} (h : Ret r) (h4 : r + 4 ≠ 0) (h11 : r + 11 ≠ 0) :
    Kernel.writeRefused r = true := by
  rcases h with rfl | rfl | h
  · exact absurd (by decide) h4
  · exact absurd (by decide) h11
  · exact h

/-- **The instruction steps**: off the `svc` cells, a code state moves to a
code state with the same result, never into the refused branch from outside
it. -/
theorem next {n : Nat} {r : BitVec 64} {m : MachineData} (h : Live n r m) (h5 : n ≠ 5) (h13 : n ≠ 13)
    (h17 : n ≠ 17) : ∃ n' m', isaLSE2.exec (atI n m) = some (.done (atI n' m')) ∧ Live n' r m' ∧
      (6 ≤ n' → n' ≤ 13 → 6 ≤ n ∧ n ≤ 13) := by
  match n, h with
  | 1, _ => exact ⟨_, _, exec1 m, by simp only [Live]; rsimp, by omega⟩
  | 2, h => exact ⟨_, _, exec2 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 3, h => exact ⟨_, _, exec3 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 4, h => exact ⟨_, _, exec4 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 6, h => exact ⟨_, _, exec6 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 7, h =>
    simp only [Live] at h
    have hx : m.regs.getRegOrZr (.low (.reg .X9) .W64) = r + 4 := by rsimp; exact h.2.1
    rw [exec7]
    by_cases hc : m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0
    · exact ⟨15, m, by simp only [hc, ↓reduceIte], trivial, by omega⟩
    · exact ⟨8, m, by simp only [hc, ↓reduceIte], ⟨h.1, h.2.2, hx ▸ hc⟩, by omega⟩
  | 8, h => exact ⟨_, _, exec8 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 9, h =>
    simp only [Live] at h
    have hx : m.regs.getRegOrZr (.low (.reg .X9) .W64) = r + 11 := by rsimp; exact h.1
    rw [exec9]
    by_cases hc : m.regs.getRegOrZr (.low (.reg .X9) .W64) = 0
    · exact ⟨15, m, by simp only [hc, ↓reduceIte], trivial, by omega⟩
    · exact ⟨10, m, by simp only [hc, ↓reduceIte], refused_of h.2.1 h.2.2 (hx ▸ hc), by omega⟩
  | 10, h => exact ⟨_, _, exec10 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 11, h => exact ⟨_, _, exec11 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 15, _ => exact ⟨_, _, exec15 m, by simp only [Live]; rsimp, by omega⟩
  | 16, h => exact ⟨_, _, exec16 m, by simp only [Live] at h ⊢; rsimp; exact h, by omega⟩
  | 5, _ => exact absurd rfl h5
  | 13, _ => exact absurd rfl h13
  | 17, _ => exact absurd rfl h17

/-! ## The `svc` cells -/

theorem atSvc5 (m : MachineData) : atSvc (atI 5 m) = true :=
  atSvc_of_cellAt (cellSv (n := 5) (by decide +kernel) (by decide) m)

theorem atSvc13 (m : MachineData) : atSvc (atI 13 m) = true :=
  atSvc_of_cellAt (cellSv (n := 13) (by decide +kernel) (by decide) m)

theorem atSvc17 (m : MachineData) : atSvc (atI 17 m) = true :=
  atSvc_of_cellAt (cellSv (n := 17) (by decide +kernel) (by decide) m)

/-- Off the `svc` cells no code state is at a system call. -/
theorem atSvc_off {n : Nat} {r : BitVec 64} {m : MachineData} (h : Live n r m) (h5 : n ≠ 5) (h13 : n ≠ 13)
    (h17 : n ≠ 17) : atSvc (atI n m) = false := by
  have hno : ∀ {n : Nat} {d : Directive}, HeadAt n d → n ≤ 18 → (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) →
      atSvc (atI n m) = false := fun hd hn hs => atSvc_false_of_cellAt (cell hd hn m) hs
  match n, h with
  | 1, _ => exact hno (d := mz .X0 2) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 2, _ => exact hno (d := mz .X1 0) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 3, _ => exact hno (d := mz .X2 0) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 4, _ => exact hno (d := mz .X8 64) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 6, _ => exact hno (d := ad 4) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 7, _ => exact hno (d := cz) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 8, _ => exact hno (d := ad 11) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 9, _ => exact hno (d := cz) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 10, _ => exact hno (d := mz .X0 101) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 11, _ => exact hno (d := mz .X8 94) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 15, _ => exact hno (d := mz .X0 42) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 16, _ => exact hno (d := mz .X8 94) (by decide +kernel) (by decide) (by intro _ h; cases h)
  | 5, _ => exact absurd rfl h5
  | 13, _ => exact absurd rfl h13
  | 17, _ => exact absurd rfl h17

/-- At directive 5 the call is `write(2, 0, 0)`. -/
theorem decode5 {r : BitVec 64} {m : MachineData} (h : Live 5 r m) :
    Kernel.decode abi.nrs (abi.nr (atI 5 m)) (abi.arg (atI 5 m)) = some (.write 2 0 0) := by
  obtain ⟨h0, h1, h2, h8⟩ := h
  show Kernel.decode Kernel.Nrs.a64 m.regs.X8.toNat (fun i => ((xRegs m.regs).getD i.val 0).toNat) = _
  simp [h0, h1, h2, h8, xRegs, Kernel.decode, Kernel.Nrs.a64]

/-- At directive 13 the call is `exit_group(101)`. -/
theorem decode13 {r : BitVec 64} {m : MachineData} (h : Live 13 r m) :
    Kernel.decode abi.nrs (abi.nr (atI 13 m)) (abi.arg (atI 13 m)) = some (.exitGroup 101) := by
  obtain ⟨-, h0, h8⟩ := h
  show Kernel.decode Kernel.Nrs.a64 m.regs.X8.toNat (fun i => ((xRegs m.regs).getD i.val 0).toNat) = _
  simp [h0, h8, xRegs, Kernel.decode, Kernel.Nrs.a64]

/-- At directive 17 the call is `exit_group(42)`. -/
theorem decode17 {r : BitVec 64} {m : MachineData} (h : Live 17 r m) :
    Kernel.decode abi.nrs (abi.nr (atI 17 m)) (abi.arg (atI 17 m)) = some (.exitGroup 42) := by
  obtain ⟨h0, h8⟩ := h
  show Kernel.decode Kernel.Nrs.a64 m.regs.X8.toNat (fun i => ((xRegs m.regs).getD i.val 0).toNat) = _
  simp [h0, h8, xRegs, Kernel.decode, Kernel.Nrs.a64]

/-- **Every result the kernel may return to the `write` is one the code
handles**: `0` and every error are `Ret`. -/
theorem ret_of_results {r : BitVec 64} (h : r ∈ Kernel.results (.write 2 0 0)) : Ret r := by
  simp only [Kernel.results, List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨a, ha, rfl⟩ | ⟨e, he, rfl⟩
  · obtain rfl : a = 0 := by omega
    exact .inr (.inr rfl)
  · by_cases h4 : e + 1 = Kernel.eintr
    · exact .inl (by rw [h4])
    by_cases h11 : e + 1 = Kernel.eagain
    · exact .inr (.inl (by rw [h11]))
    refine .inr (.inr ?_)
    have hn : ∀ k, k < 2 ^ 64 → 0 < k → (Kernel.neg k).toNat = 2 ^ 64 - k := by
      intro k hk hk0
      simp only [Kernel.neg, BitVec.toNat_neg, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]
    have hm : Kernel.maxErrno = 4095 := rfl
    have hne : ∀ k, k < 4096 → 0 < k → k ≠ e + 1 → Kernel.neg (e + 1) ≠ Kernel.neg k := by
      intro k hk hk0 hke heq
      have := congrArg BitVec.toNat heq
      rw [hn _ (by omega) (by omega), hn _ (by omega) hk0] at this
      omega
    simp only [Kernel.writeRefused, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      bne_iff_ne, ne_eq]
    refine .inr ⟨⟨?_, hne _ (by decide) (by decide) (Ne.symm h4)⟩, hne _ (by decide) (by decide) (Ne.symm h11)⟩
    rw [hn _ (by omega) (by omega)]
    omega

/-! ## Certification steps -/

/-- The machine data after the `write` returns `r`. -/
def retD (r : BitVec 64) (m : MachineData) : MachineData :=
  { m with regs := { m.regs with X0 := UInt64.ofNat r.toNat } }

/-- **The `write` returns** to directive 6 with `r` in `x0`. -/
theorem ret5 (m : MachineData) (r : BitVec 64) : abi.ret (atI 5 m) r = atI 6 (retD r m) := by
  rw [abi_ret_of_cellAt (cellSv (n := 5) (by decide +kernel) (by decide) m)]
  simp only [svcRet, after, atI, retD]
  rw [show Kraken.Executable.addrOf st0.exe 5 + Int64.ofNat 4 = Kraken.Executable.addrOf st0.exe 6 by
    decide +kernel]

theorem live_retD {r : BitVec 64} (h : Ret r) (m : MachineData) : Live 6 r (retD r m) :=
  ⟨by simp [retD], h⟩

/-- The code states. -/
def Code (s : State) : Prop := ∃ n r m, s = atI n m ∧ Live n r m

/-- **A certification step from a code state** keeps the promises and
reaches a code state: an instruction, or a return of the `write`; at the
`exit_group` cells there is none. -/
theorem certStep {μ : Marks} {x : Kernel.KState} {tid : Nat} {t : Thread isaLSE2} {mem : Memory}
    {q : Thread isaLSE2 × Memory} (hμ : ∀ k, μ.site k = none) (hc : Code t.st)
    (h : ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ Code q.1.st := by
  have hsi : ∀ s, Kernel.siteAt abi μ s = none := fun s => by simp [Kernel.siteAt, hμ]
  obtain ⟨n, r, m, hst, hl⟩ := hc
  by_cases h5 : n = 5
  · subst h5
    obtain ⟨outs, o, hso, ho, rfl⟩ := h
    have hex : ∃ tr, (Kernel.certSem abi Arch.armv8 μ x tid).exec t.st = some tr := by
      have ha : abi.atSys (atI 5 m) = true := atSvc5 m
      simp only [Kernel.certSem, hst, Kernel.soloExec, Kernel.siteAt, hμ, reduceCtorEq, ite_false, ha, ite_true,
        decode5 hl]
      exact ⟨_, rfl⟩
    obtain ⟨tr, htr⟩ := hex
    obtain ⟨hq, hL⟩ := Kernel.soloExec_sys (K := abi) (hsi _) (hst ▸ atSvc5 m) (hst ▸ decode5 hl)
      (by simp) htr
    obtain ⟨-, hpr, hlf⟩ := Kernel.stepOneWith_quiet htr hq hso ho
    refine ⟨hpr, ?_⟩
    have hP := hL _ hlf
    simp only [Kernel.certSuccs, List.mem_map] at hP
    obtain ⟨r', hr', he⟩ := hP
    show Code o.thread.st
    rw [← he, hst, ret5]
    exact ⟨6, r', _, rfl, live_retD (ret_of_results hr') m⟩
  have hdead : ∀ {v n}, Live n r m → abi.atSys (atI n m) = true →
      Kernel.decode abi.nrs (abi.nr (atI n m)) (abi.arg (atI n m)) = some (.exitGroup v) → t.st = atI n m →
      ¬ ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x tid) tid (t, mem) q := by
    intro v n _ ha hd hs
    refine stepC_dead (n := 0) (f := fun i => .done ([] : List isaLSE2.State)[i]) ?_ rfl
    simp only [Kernel.certSem, hs, Kernel.soloExec, Kernel.siteAt, hμ, reduceCtorEq, ite_false, ha, ite_true, hd,
      Kernel.results, List.filterMap_nil]
    rfl
  by_cases h13 : n = 13
  · subst h13; exact absurd h (hdead hl (atSvc13 m) (decode13 hl) hst)
  by_cases h17 : n = 17
  · subst h17; exact absurd h (hdead hl (atSvc17 m) (decode17 hl) hst)
  obtain ⟨n', m', hex, hl', -⟩ := next hl h5 h13 h17
  have hce : (Kernel.certSem abi Arch.armv8 μ x tid).exec t.st = some (.done (atI n' m')) := by
    show Kernel.soloExec abi Arch.armv8 μ x tid t.st = _
    rw [hst, Kernel.soloExec_of_not_atSys abi (hsi _) (atSvc_off hl h5 h13 h17)]; exact hex
  obtain ⟨-, hpr, hP⟩ := stepC_silent hce (silentTree_done _) h
  exact ⟨hpr, n', r, m', hP, hl'⟩

/-- **No certification from a code state empties a promise set** (with no
transfer site in the marks). -/
theorem no_certOkC {μ : Marks} {x : Kernel.KState} {tid : Nat} {t : Thread isaLSE2} {mem : Memory}
    (hμ : ∀ k, μ.site k = none) (hc : Code t.st) (hp : t.prom ≠ []) :
    ¬ CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x tid) tid t mem :=
  no_certOkC_of_closed (fun _ _ _ hc hs => certStep hμ hc hs) hc hp

/-! ## The marks -/

/-- **The abort site**: only `writeErr`'s label resolves, to directive 13. -/
theorem abortAt_eq (hp : textProgram toy2Asm = .ok toy2Prog) (k : AbortKind) :
    (T.marks toy2Asm Λ).abortAt k = if k = .writeErr then some 60 else none := by
  refine (resolve_of_parsed (kernel 1) Entry.linux Λ hp _).trans ?_
  cases k <;> decide +kernel

/-- **No transfer site resolves.** -/
theorem site_none (hp : textProgram toy2Asm = .ok toy2Prog) (k : XferKind) :
    (T.marks toy2Asm Λ).site k = none := by
  refine (resolve_of_parsed (kernel 1) Entry.linux Λ hp _).trans ?_
  cases k <;> decide +kernel

theorem pc13 (m : MachineData) : T.M.pc (atI 13 m) = 60 := by
  show (Kraken.Executable.addrOf st0.exe 13).toBitVec.toNat = 60
  decide +kernel

theorem pc17 (m : MachineData) : T.M.pc (atI 17 m) ≠ 60 := by
  show (Kraken.Executable.addrOf st0.exe 17).toBitVec.toNat ≠ 60
  decide +kernel

/-! ## The target phases -/

/-- **A live phase**: one thread, at a code state, with no promise; memory
and kernel state as loaded. -/
def LiveC (n : Nat) (r : BitVec 64) (t : T.M.Cfg) : Prop :=
  ∃ th m, t.1.threads = #[th] ∧ th.prom = [] ∧ t.1.mem = mem0 ∧ t.2 = K0 ∧ th.st = atI n m ∧ Live n r m

/-- **The process has ended** with outcome `o`. -/
def Ended (o : Scc.Sem.Outcome) (t : T.M.Cfg) : Prop :=
  ∃ th, t.1.threads = #[th] ∧ t.1.mem = mem0 ∧ t.2 = { K0 with exited := some o }

/-- A thread at an `svc` may take a kernel step. -/
theorem ready_on {t : Config isaLSE2 × Kernel.KState} {th : Thread isaLSE2} (hk : t.2 = K0) (h : atSvc th.st = true) :
    Kernel.ready abi 0 t th = true := by
  simp only [Kernel.ready, hk]
  rw [show abi.atSys th.st = atSvc th.st from rfl, h]
  decide +kernel

/-- **The `write` steps**: it returns `r'` (one the code handles), with no
event for `-EINTR` and `-EAGAIN`, and `writeErr` for a refusal. -/
theorem sys5 {t t' : Config isaLSE2 × Kernel.KState} {th : Thread isaLSE2} {r : BitVec 64} {m : MachineData}
    {p : Kernel.Pick} {es : List Ev} (hth : t.1.threads = #[th]) (hk : t.2 = K0) (hst : th.st = atI 5 m)
    (hl : Live 5 r m)
    (h : Kernel.sysStep abi Arch.armv8 0 t p = some (es, t')) :
    ∃ r', Ret r' ∧ t' = (t.1.withThread 0 (Kernel.retThread abi th r') t.1.mem, K0) ∧
      ((es = [] ∧ Kernel.writeRefused r' = false) ∨ es = [.writeErr]) := by
  have ht1 : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hr : Kernel.ready abi 0 t th = true := ready_on hk (hst ▸ atSvc5 m)
  have hc : Kernel.callOf abi th = some (.write 2 0 0) := by rw [Kernel.callOf, hst]; exact decode5 hl
  have hwr : t.2.wr 0 = 0 := by rw [hk]; decide +kernel
  simp only [Kernel.sysStep, ht1, hr, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases p with
  | byte rd => simp [hwr] at h
  | ret r' =>
    simp only [hwr, Nat.lt_irrefl, ↓reduceIte] at h
    split at h
    · rename_i he
      simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨r', he.elim .inl (.inr ∘ .inl), by rw [hk], .inl ⟨rfl, ?_⟩⟩
      rcases he with rfl | rfl <;> decide
    · split at h
      · rename_i hw
        simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨r', .inr (.inr hw), by rw [hk], .inr rfl⟩
      · cases h
  | abort k => simp at h

theorem callOf13 {th : Thread isaLSE2} {r : BitVec 64} {m : MachineData} (hst : th.st = atI 13 m)
    (hl : Live 13 r m) : Kernel.callOf abi th = some (.exitGroup 101) := by
  rw [Kernel.callOf, hst]; exact decode13 hl

theorem callOf17 {th : Thread isaLSE2} {r : BitVec 64} {m : MachineData} (hst : th.st = atI 17 m)
    (hl : Live 17 r m) : Kernel.callOf abi th = some (.exitGroup 42) := by
  rw [Kernel.callOf, hst]; exact decode17 hl

theorem callOf5 {th : Thread isaLSE2} {r : BitVec 64} {m : MachineData} (hst : th.st = atI 5 m)
    (hl : Live 5 r m) : Kernel.callOf abi th = some (.write 2 0 0) := by
  rw [Kernel.callOf, hst]; exact decode5 hl

/-- **The steps of a live phase**: an instruction (no event, a live phase;
the refused branch is entered only by the `write`), the `write` (no event
or `writeErr`), `exit_group(42)` (`exit 42`), or, at the abort site,
`exit_group(101)` as `abort writeErr`. -/
theorem live_step (hp : textProgram toy2Asm = .ok toy2Prog) {n : Nat} {r : BitVec 64} {t t' : T.M.Cfg}
    {tid : Nat} {es : List Ev} (h : LiveC n r t) (hs : T.M.Step (T.marks toy2Asm Λ) tid t es t') :
    (es = [] ∧ ∃ n' r', LiveC n' r' t' ∧
        (6 ≤ n' → n' ≤ 13 → Kernel.writeRefused r' = true → 6 ≤ n ∧ n ≤ 13 ∧ r' = r)) ∨
      (es = [.writeErr] ∧ ∃ r', LiveC 6 r' t') ∨
      (es = [.exit (Kernel.exitCode 42)] ∧ Ended (.exit (Kernel.exitCode 42)) t') ∨
      (es = [.abort .writeErr] ∧ n = 13 ∧ Ended (.abort .writeErr) t') := by
  obtain ⟨th, m, hth, hpr, hm, hk, hst, hl⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hsvc : ∀ {k : Nat}, (∀ m, atSvc (atI k m) = true) → n = k → atSvc th.st = true := by
    intro k hk e; subst e; rw [hst]; exact hk m
  have hoff : n ≠ 5 → n ≠ 13 → n ≠ 17 → atSvc th.st = false := fun h5 h13 h17 => by
    rw [hst]; exact atSvc_off hl h5 h13 h17
  cases hs with
  | instr _ hns _ hstep =>
    have hn : ∀ {k : Nat}, (∀ m, atSvc (atI k m) = true) → n ≠ k := fun hk e => hns ⟨th, ht1, hsvc hk e⟩
    have h5 := hn atSvc5
    have h13 := hn atSvc13
    have h17 := hn atSvc17
    rcases hstep with hi | ⟨t2, w, ht2, -, hcert, -⟩
    · obtain ⟨n', m', hex, hl', hfl⟩ := next hl h5 h13 h17
      obtain ⟨th', hfin, -, rfl⟩ := (ExtMachine.instrSemC_done_iff ht1 (hst ▸ hex)).mp hi
      refine .inl ⟨rfl, n', r, ⟨th', m', by simp only [Config.withThread, hth]; rfl,
        (finishInstr_relKey hfin).1.trans hpr, hm, hk, finishInstr_st hfin, hl'⟩, fun a b _ => ?_⟩
      exact ⟨(hfl a b).1, (hfl a b).2, rfl⟩
    · obtain rfl := Option.some.inj (ht2.symm.trans ht1)
      exact absurd hcert (no_certOkC (site_none hp) ⟨n, r, m, hst, hl⟩ (by simp))
  | spawn _ hsp =>
    obtain ⟨j, r', hsp, -⟩ := hsp
    by_cases h5 : n = 5
    · subst h5; simp [Kernel.spawnStep, ht1, ready_on hk (hsvc atSvc5 rfl), callOf5 hst hl] at hsp
    by_cases h13 : n = 13
    · subst h13; simp [Kernel.spawnStep, ht1, ready_on hk (hsvc atSvc13 rfl), callOf13 hst hl] at hsp
    by_cases h17 : n = 17
    · subst h17; simp [Kernel.spawnStep, ht1, ready_on hk (hsvc atSvc17 rfl), callOf17 hst hl] at hsp
    simp [Kernel.spawnStep, ht1, not_ready (hoff h5 h13 h17)] at hsp
  | sys _ hsys _ habt hexit =>
    obtain ⟨p, hsys, -⟩ := hsys
    by_cases h5 : n = 5
    · subst h5
      obtain ⟨r', hr', rfl, hes⟩ := sys5 hth hk hst hl hsys
      have hl6 : LiveC 6 r' (t.1.withThread 0 (Kernel.retThread abi th r') t.1.mem, K0) := by
        refine ⟨Kernel.retThread abi th r', retD r' m, by simp only [Config.withThread, hth]; rfl,
          (Kernel.retThread_prom (K := abi) th r').trans hpr, hm, rfl, ?_, live_retD hr' m⟩
        exact (Kernel.retThread_st (K := abi) th r').trans (hst ▸ ret5 m r')
      rcases hes with ⟨rfl, hw⟩ | rfl
      · exact .inl ⟨rfl, 6, r', hl6, fun _ _ h => absurd h (by rw [hw]; decide)⟩
      · exact .inr (.inl ⟨rfl, r', hl6⟩)
    by_cases h13 : n = 13
    · subst h13
      obtain ⟨-, call, hcall, hcases⟩ := Kernel.sysStep_cases ht1 hsys (fun _ _ _ h => by
        rw [callOf13 hst hl] at h; cases h)
      rw [callOf13 hst hl] at hcall
      cases hcall
      rcases hcases with ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, hg, _⟩ | ⟨h, _⟩ | ⟨v, hv, hx⟩
      · cases h
      · exact absurd rfl (hg 101)
      · cases h
      cases hv
      rcases hx with ⟨-, rfl, -⟩ | ⟨k, -, -, rfl, rfl⟩
      · exact absurd ⟨th, ht1, by rw [hst]; exact pc13 m⟩
          (hexit _ (List.mem_singleton_self _) .writeErr 60 (by rw [abortAt_eq hp]; rfl))
      · obtain ⟨a, ha, -⟩ := habt k (List.mem_singleton_self _)
        rw [abortAt_eq hp] at ha
        split at ha
        · subst k
          exact .inr (.inr (.inr ⟨rfl, rfl, th, hth, hm, by rw [hk]⟩))
        · cases ha
    by_cases h17 : n = 17
    · subst h17
      obtain ⟨-, call, hcall, hcases⟩ := Kernel.sysStep_cases ht1 hsys (fun _ _ _ h => by
        rw [callOf17 hst hl] at h; cases h)
      rw [callOf17 hst hl] at hcall
      cases hcall
      rcases hcases with ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, hg, _⟩ | ⟨h, _⟩ | ⟨v, hv, hx⟩
      · cases h
      · exact absurd rfl (hg 42)
      · cases h
      cases hv
      rcases hx with ⟨-, rfl, rfl⟩ | ⟨k, -, hv, -⟩
      · exact .inr (.inr (.inl ⟨rfl, th, hth, hm, by rw [hk]⟩))
      · exact absurd hv (by decide)
    simp [Kernel.sysStep, ht1, not_ready (hoff h5 h13 h17)] at hsys
  | xfer k _ hsite _ =>
    obtain ⟨a, ha, -⟩ := hsite
    rw [site_none hp] at ha; cases ha

/-! ## Progress -/

theorem exec_sv {n : Nat} (hd : HeadAt n sv) (hn : n ≤ 18) (m : MachineData) :
    isaLSE2.exec (atI n m) = some (.fault (pendingSyscallMsg 0)) :=
  exec_svc (cellSv hd hn m)

/-- No thread at a code state has halted. -/
theorem not_halted {th : Thread isaLSE2} {n : Nat} {r : BitVec 64} {m : MachineData} (hst : th.st = atI n m)
    (hl : Live n r m) : th.halted = false := by
  by_cases h5 : n = 5
  · subst h5; simp [Thread.halted, hst, exec_sv (n := 5) (by decide +kernel) (by decide) m]
  by_cases h13 : n = 13
  · subst h13; simp [Thread.halted, hst, exec_sv (n := 13) (by decide +kernel) (by decide) m]
  by_cases h17 : n = 17
  · subst h17; simp [Thread.halted, hst, exec_sv (n := 17) (by decide +kernel) (by decide) m]
  obtain ⟨n', m', hex, -⟩ := next hl h5 h13 h17
  simp [Thread.halted, hst, hex]

/-- **`-EINTR`**: the `write` may always return. -/
theorem sys5_eintr {μ : Marks} {t : Config isaLSE2 × Kernel.KState} {th : Thread isaLSE2} {r : BitVec 64}
    {m : MachineData}
    (ht : t.1.threads[0]? = some th) (hk : t.2 = K0) (hpr : th.prom = []) (hst : th.st = atI 5 m)
    (hl : Live 5 r m) :
    (Kernel.hooks abi Arch.armv8 1).sys μ 0 t []
      (t.1.withThread 0 (Kernel.retThread abi th (Kernel.neg Kernel.eintr)) t.1.mem, t.2) := by
  have hr : Kernel.ready abi 0 t th = true := ready_on hk (hst ▸ atSvc5 m)
  have hwr : t.2.wr 0 = 0 := by rw [hk]; decide +kernel
  exact ⟨.ret (Kernel.neg Kernel.eintr), by simp [Kernel.sysStep, ht, hr, callOf5 hst hl, hwr, Kernel.back] <;> rfl,
    Kernel.certAfter_of_prom abi (Kernel.prom_withThread ht hpr (by simp [hpr]))⟩

/-- **`exit_group(101)` at the abort site** may end the process as
`abort writeErr`. -/
theorem sys13_abort {μ : Marks} {t : Config isaLSE2 × Kernel.KState} {th : Thread isaLSE2} {r : BitVec 64}
    {m : MachineData}
    (ht : t.1.threads[0]? = some th) (hk : t.2 = K0) (hpr : th.prom = []) (hst : th.st = atI 13 m)
    (hl : Live 13 r m) :
    (Kernel.hooks abi Arch.armv8 1).sys μ 0 t [.abort .writeErr]
      (t.1, { t.2 with exited := some (.abort .writeErr) }) := by
  have hr : Kernel.ready abi 0 t th = true := ready_on hk (hst ▸ atSvc13 m)
  exact ⟨.abort .writeErr, by simp [Kernel.sysStep, ht, hr, callOf13 hst hl, Kernel.abortStatus] <;> rfl,
    Kernel.certAfter_of_prom abi fun t' h' => by rw [ht] at h'; cases h'; exact hpr⟩

/-- **A live phase has progress**: no fault, and the thread steps (an
instruction, the `write` returning `-EINTR`, `abort writeErr` at the abort
site, or `exit_group(42)`). -/
theorem live_progress (hp : textProgram toy2Asm = .ok toy2Prog) {n : Nat} {r : BitVec 64} {t : T.M.Cfg}
    (h : LiveC n r t) : T.M.Progress (T.marks toy2Asm Λ) t := by
  obtain ⟨th, m, hth, hpr, hm, hk, hst, hl⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hsvc : ∀ {k : Nat}, (∀ m, atSvc (atI k m) = true) → n = k → atSvc th.st = true := by
    intro k hk e; subst e; rw [hst]; exact hk m
  have hoff : n ≠ 5 → n ≠ 13 → n ≠ 17 → atSvc th.st = false := fun h5 h13 h17 => by
    rw [hst]; exact atSvc_off hl h5 h13 h17
  refine ⟨?_, .inr ⟨⟨0, by rw [hk]; rfl, (runs_pre hth hk).2.2, th, ht, fun h => by
    rw [not_halted hst hl] at h; cases h.1⟩, fun tid hlv => ?_⟩⟩
  · rintro (⟨tid, m', ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm'⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.armv8 th 0 t.1.mem = some outs := by
        simp only [stepThread, ht1] at hs; exact hs
      have hn : ∀ {k : Nat}, (∀ m, atSvc (atI k m) = true) → n ≠ k := fun hk e => hns ⟨th, ht1, hsvc hk e⟩
      obtain ⟨n', m'', hex, -⟩ := next hl (hn atSvc5) (hn atSvc13) (hn atSvc17)
      exact Spike.Bridge.stepOne_no_error Arch.armv8 (hst ▸ hex) (Spike.Bridge.runTree_done_ok Arch.armv8 _ _ _ _)
        hs' m' hm'
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [not_halted hst hl, Bool.or_false] at hf
        by_cases h5 : n = 5
        · subst h5; simp [callOf5 hst hl] at hf
        by_cases h13 : n = 13
        · subst h13; simp [callOf13 hst hl] at hf
        by_cases h17 : n = 17
        · subst h17; simp [callOf17 hst hl] at hf
        rw [show abi.atSys th.st = atSvc th.st from rfl, hoff h5 h13 h17] at hf
        simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hn : ∀ {k : Nat}, (∀ m, atSvc (atI k m) = true) → n ≠ k := fun hk e =>
        absurd ((hsvc hk e).symm.trans hns) (by decide)
      obtain ⟨n', m'', hex', -⟩ := next hl (hn atSvc5) (hn atSvc13) (hn atSvc17)
      rw [hst, hex'] at hex; cases hex; cases htouch
  · obtain ⟨-, -, t1, ht1, -⟩ := hlv
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    have hsite : ∀ k, ¬ T.M.AtSite (T.marks toy2Asm Λ) k t 0 := fun k ⟨a, ha, _⟩ => by
      rw [site_none hp] at ha; cases ha
    by_cases h5 : n = 5
    · subst h5
      exact ⟨_, _, .sys (runs_pre hth hk) (sys5_eintr ht1 hk hpr hst hl) (by simp) (fun k hk => by simp at hk)
        (fun e he => by simp at he)⟩
    by_cases h13 : n = 13
    · subst h13
      refine ⟨_, _, .sys (runs_pre hth hk) (sys13_abort ht1 hk hpr hst hl) (by simp) (fun k hk => ?_)
        (fun e he => by simp at he)⟩
      obtain rfl : k = .writeErr := by simpa using hk
      exact ⟨60, by rw [abortAt_eq hp]; rfl, th, ht1, by rw [hst]; exact pc13 m⟩
    by_cases h17 : n = 17
    · subst h17
      refine ⟨_, _, .sys (runs_pre hth hk)
        (Kernel.sys_exitGroup (K := abi) Arch.armv8 1 ht1 (ready_on hk (hsvc atSvc17 rfl)) hpr (callOf17 hst hl))
        (by simp) (fun k hk => by simp at hk) (fun _ _ k a ha => ?_)⟩
      rw [abortAt_eq hp] at ha
      split at ha
      · cases ha
        rintro ⟨t2, ht2, hpc⟩
        cases Option.some.inj (ht2.symm.trans ht1)
        exact pc17 m (hst ▸ hpc)
      · cases ha
    obtain ⟨n', m', hex, -⟩ := next hl h5 h13 h17
    obtain ⟨th', hfin⟩ := Spike.Bridge.finishInstr_nonempty th (isaLSE2.deps th.st)
      (instrViews th (isaLSE2.deps th.st)) (atI n' m') (Live.TicketStep.ctx0 0 th t.1.mem)
    have hi := (ExtMachine.instrSemC_done_iff (A := Arch.armv8)
      (cexec := Kernel.certSem abi Arch.armv8 (T.marks toy2Asm Λ) t.2 0) ht1
      (hst ▸ hex)).mpr ⟨th', hfin, certOkC_of_prom_nil ((finishInstr_relKey hfin).1.trans hpr), rfl⟩
    exact ⟨[], _, .instr (runs_pre hth hk) (fun ⟨t2, ht2, h2⟩ => by
      rw [ht1] at ht2; cases ht2; exact absurd ((hoff h5 h13 h17).symm.trans h2) (by decide)) hsite (.inl hi)⟩

/-- **After the end there is progress**: the process has exited, with no
fault. -/
theorem ended_progress {μ : Marks} {o : Scc.Sem.Outcome} {t : T.M.Cfg} (h : Ended o t) : T.M.Progress μ t := by
  obtain ⟨th, -, -, hk⟩ := h
  refine ⟨?_, .inl ?_⟩
  · rintro (⟨tid, m, ⟨-, hx, -⟩, -⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, -, -, hx, -⟩))
    · rw [hk] at hx; cases hx
    · unfold Kernel.faultAt at hf
      split at hf
      · rw [hk] at hf; simp at hf
      · cases hf
    · rw [hk] at hx; cases hx
  · show (match (kernel 1).exited t.2 with
      | some o => some o
      | none => if t.1.final then some .halted else none).isSome
    rw [show (kernel 1).exited t.2 = t.2.exited from rfl, hk]; rfl

/-- After the end no thread steps. -/
theorem ended_no_step {μ : Marks} {o : Scc.Sem.Outcome} {t t' : T.M.Cfg} {tid : Nat} {es : List Ev}
    (h : Ended o t) (hs : T.M.Step μ tid t es t') : False := by
  obtain ⟨-, -, -, hk⟩ := h
  obtain ⟨-, hx, -⟩ := hs.runs
  rw [hk] at hx
  cases hx

/-! ## The load -/

/-- The loaded configuration. -/
def t0 : T.M.Cfg := loadProg (kernel 1) Entry.linux Λ toy2Prog [] (imageMem Λ ++ wordsMem [])

/-- **The load**, from the parse of the text. -/
theorem load_eq (hp : textProgram toy2Asm = .ok toy2Prog) (hd : dataSections toy2Asm = some {}) :
    T.load toy2Asm Λ = some t0 := by
  refine (load_of_parsed (kernel 1) Entry.linux Λ hp hd).trans ?_
  rw [loadParsed]
  split
  · rfl
  · rename_i h; exact absurd (by decide +kernel) h

theorem st0_eq : st0 = atI 1 st0.st.1 := by
  have h : st0.st.2 = Kraken.Executable.addrOf st0.exe 1 := by decide +kernel
  simp only [atI]; rw [← h]

theorem live_t0 : LiveC 1 0 t0 := ⟨_, st0.st.1, rfl, rfl, rfl, rfl, st0_eq, trivial⟩

/-! ## The trace invariant -/

/-- **The trace invariant**: in the refused branch (directives 6 to 13 with
a refused result), the trace has the refusal; or the process has ended. -/
def Inv (tr : List Ev) (t : T.M.Cfg) : Prop :=
  (∃ n r, LiveC n r t ∧ (6 ≤ n → n ≤ 13 → Kernel.writeRefused r = true → Ev.writeErr ∈ tr)) ∨
    ∃ o, Ended o t

theorem inv_step (hp : textProgram toy2Asm = .ok toy2Prog) {pre es : List Ev} {t t' : T.M.Cfg} {tid : Nat}
    (h : Inv pre t) (hs : T.M.Step (T.marks toy2Asm Λ) tid t es t') : Inv (pre ++ es) t' := by
  rcases h with ⟨n, r, hl, hf⟩ | ⟨o, he⟩
  · rcases live_step hp hl hs with ⟨rfl, n', r', hl', hfl⟩ | ⟨rfl, r', hl'⟩ | ⟨rfl, he'⟩ | ⟨rfl, -, he'⟩
    · refine .inl ⟨n', r', hl', fun a b c => ?_⟩
      obtain ⟨a', b', rfl⟩ := hfl a b c
      rw [List.append_nil]; exact hf a' b' c
    · exact .inl ⟨6, r', hl', fun _ _ _ => List.mem_append_right _ (List.mem_singleton_self _)⟩
    · exact .inr ⟨_, he'⟩
    · exact .inr ⟨_, he'⟩
  · exact (ended_no_step he hs).elim

theorem inv_run (hp : textProgram toy2Asm = .ok toy2Prog) {t t' : T.M.Cfg} {tr : List Ev}
    (hr : T.M.Run (T.marks toy2Asm Λ) t tr t') : ∀ {pre}, Inv pre t → Inv (pre ++ tr) t' := by
  induction hr with
  | refl => intro pre h; rwa [List.append_nil]
  | step hs _ ih =>
    intro pre h
    obtain ⟨tid, hs⟩ := hs
    rw [← List.append_assoc]
    exact ih (inv_step hp h hs)

/-! ## The simulation -/

/-- **The relation**: before the exit (or after the abort) with the start,
after the exit with `main` at `ret 42`. -/
def R (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ((∃ n r, LiveC n r t) ∨ Ended (.abort .writeErr) t) ∧ s = s0 ∨ Ended (.exit (Kernel.exitCode 42)) t ∧ s = s1

theorem components_R {t : T.M.Cfg} {s : TermRun.Cfg} (h : R t s) : Components T.M Λ wit t (S.core s) := by
  rcases h with ⟨⟨n, r, th, m, hth, -, -, hk, -⟩ | ⟨th, hth, -, hk⟩, rfl⟩ | ⟨⟨th, hth, -, hk⟩, rfl⟩
  · exact components hth (by rw [hk]; rfl) (.inl rfl)
  · exact components hth (by rw [hk]; rfl) (.inl rfl)
  · exact components hth (by rw [hk]; rfl) (.inr rfl)

/-- **The step-wise simulation.** -/
theorem stepSim (hp : textProgram toy2Asm = .ok toy2Prog) (hd : dataSections toy2Asm = some {}) :
    StepSim T S Λ toy2Asm R where
  init t h := by
    rw [load_eq hp hd] at h
    cases h
    exact ⟨s0, rfl, .inl ⟨.inl ⟨1, 0, live_t0⟩, rfl⟩⟩
  step tid t es t' s hR hs := by
    rcases hR with ⟨⟨n, r, h⟩ | h, rfl⟩ | ⟨h, -⟩
    · rcases live_step hp h hs with ⟨rfl, n', r', h', -⟩ | ⟨rfl, r', h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, -, h'⟩
      · exact ⟨s0, .refl _, .inl ⟨.inl ⟨n', r', h'⟩, rfl⟩⟩
      · exact ⟨s0, .refl _, .inl ⟨.inl ⟨6, r', h'⟩, rfl⟩⟩
      · exact ⟨s1, LRun.step (es := [.exit (Kernel.exitCode 42)]) (tr := []) ⟨0, src_step⟩ (.refl _),
          .inr ⟨h', rfl⟩⟩
      · exact ⟨s0, .refl _, .inl ⟨.inr h', rfl⟩⟩
    · exact (ended_no_step h hs).elim
    · exact (ended_no_step h hs).elim

/-- **The toy text is a correct lowering of `toyP` on `canonical 1`**: a
refused `write` ends the process at the `writeErr` abort site, justified by
the refusal in the trace; given the parse of the text (`#guard`-checked
above). -/
theorem toy2_correct (hp : textProgram toy2Asm = .ok toy2Prog) (hd : dataSections toy2Asm = some {}) :
    Scc.Correct toyCfg toy2Asm toyP := by
  refine ⟨⟨rfl, ?_, by decide⟩, ?_⟩
  · show Target.threadSlots T toy2Asm Λ ≤ 1
    unfold Target.threadSlots
    rw [load_eq hp hd]
    decide +kernel
  · refine correct_of_stepSim (stepSim hp hd) trivLayout_wf ⟨t0, load_eq hp hd⟩ ?_ ?_ ?_
    · intro t0' tr t h0 hr
      obtain ⟨s, -, hR⟩ := (stepSim hp hd).reach h0 hr
      rcases hR with ⟨⟨n, r, h⟩ | h, -⟩ | ⟨h, -⟩
      · exact ⟨live_progress hp h, inLayout_mem h.choose_spec.choose_spec.2.2.1⟩
      · exact ⟨ended_progress h, inLayout_mem h.choose_spec.2.1⟩
      · exact ⟨ended_progress h, inLayout_mem h.choose_spec.2.1⟩
    · intro t0' tr t tid es t' k s h0 hr _ hR hs hk
      obtain rfl : t0' = t0 := Option.some.inj ((h0 : T.load toy2Asm Λ = some t0').symm.trans (load_eq hp hd))
      have hinv := inv_run hp hr (pre := []) (.inl ⟨1, 0, live_t0, by omega⟩)
      rw [List.nil_append] at hinv
      rcases hinv with ⟨n, r, hl, hf⟩ | ⟨o, he⟩
      · obtain ⟨th, m, hth, hpr, hm, hk0, hst, hlv⟩ := hl
        rcases live_step hp ⟨th, m, hth, hpr, hm, hk0, hst, hlv⟩ hs with
          ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl, -⟩
        · cases hk
        · simp at hk
        · simp at hk
        · obtain rfl : k = .writeErr := by simpa using hk
          obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
          obtain ⟨rfl, -⟩ := get_one hth ht1
          exact ⟨wit, 0, components_R hR, rfl, hf (by decide) (by decide) hlv.1⟩
      · exact (ended_no_step he hs).elim
    · intro t s h
      exact ⟨wit, components_R h⟩

end Spike.Lib.A64ExtToy2
