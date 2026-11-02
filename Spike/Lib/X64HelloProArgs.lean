/-
**A prologue keeps `wc_worker`'s and the thread worker's argument registers** (x86-64; the twin of
`Spike/Lib/A64HelloProArgs.lean`): the frame's head (`pushq %rbp; movq %rsp, %rbp`), the check's address into
`%rax`, the limit's load into `%r11`, the check and its branch, and the frame's set-up with the six spills write
none of `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9`, so a prologue's states lie inside any `W` determined by the entry's
values of those registers. Shared by the placed obligations of `wc_worker` and the thread worker.

- `ArgR`: `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9`.
- `keepA_pro`: those registers kept by every prefix of each prologue block; `keepA_xS1`, `keepA_xS2`,
  `keepA_xS3`: by the closed-form states after the head, the check's address and the limit's load.
- `xProW_args`: a prologue's states inside `W` from its entry's argument registers.

## Differences from the AArch64 version

- The packet's words are in `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9` (AArch64 `x0`, `x2 .. x5`); the offset word
  in `%rsi` (AArch64 `x1`) is no packet word.
- x86-64's prologue is `XProW`'s five pieces at both prologues' shapes (`5 9 3 z2 4`, the six spills `wcPs`, equal
  to `thrPs`): one prefix lemma `keepA_pro` over the four blocks and three closed-form lemmas replace AArch64's
  `keepA_chkHead`, `keepA_chkBr`, `keepA_frameSet`, `keepA_chkRegs`, `keepA_ldStep`.
-/
import Spike.Lib.X64HelloPlacedZEnv
import Spike.Lib.X64HelloWorkerSegRP

namespace Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xSt xS1 xS2 xS3 hdRegs)

/-! ## A prologue's states -/

section Pro

/-- The abstract run's simp set over concrete blocks (as in `X64WakePlacedZ`). -/
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

/-- The argument registers of `wc_worker`'s packet: `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9`. -/
def ArgR (r : Reg64) : Prop := r = .rdi ∨ r = .rdx ∨ r = .rcx ∨ r = .r8 ∨ r = .r9

/-- **Every prefix of a prologue block keeps the argument registers.** -/
theorem keepA_pro (l : String → Int64) (pc : Int64) (o : SO) (σ : AS) (Z : Int64) (L : String) (z2 : Nat)
    {blk : List (Directive × Nat)}
    (hb : blk = xHead ∨ blk = xLea Z 5 ∨ blk = xCmp L 3 z2 ∨ blk = xFr Z 4 Wk.wcPs)
    {k : Nat} (hk : k < blk.length) (r : Reg64) (hr : ArgR r) :
    (arun l (blk.take k) ⟨pc, o, σ⟩).σ.regs.get64 r = σ.regs.get64 r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [xHead, xLea, xCmp, xFr, xSt, Wk.wcPs, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases k with _|_|_|_|_|_|_|k <;> (try omega) <;> arun_simp

theorem keepA_xS1 (σ : AS) (r : Reg64) (hr : ArgR r) : (xS1 σ).regs.get64 r = σ.regs.get64 r := by
  simp only [xS1, hdRegs]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide)]

theorem keepA_xS2 (Z : Int64) (σ : AS) (r : Reg64) (hr : ArgR r) : (xS2 Z σ).regs.get64 r = σ.regs.get64 r := by
  simp only [xS2]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  exact keepA_xS1 σ r hr

theorem keepA_xS3 (Z : Int64) (v : BitVec 64) (σ : AS) (r : Reg64) (hr : ArgR r) :
    (xS3 Z v σ).regs.get64 r = σ.regs.get64 r := by
  simp only [xS3, Spike.Lib.X64.fsStep]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  exact keepA_xS2 Z σ r hr

/-- **A prologue's states inside `W`** from its entry's: every control of the entry invariant `J` in `W` at
every state agreeing with the entry's on the argument registers (`hW`); the prologue writes none of them. -/
theorem xProW_args {W : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {z2 : Nat}
    {J : AS → Ctl → Prop}
    (hW : ∀ σ c, J σ c → ∀ s : State, (∀ r, ArgR r → s.st.1.regs.get64 r = σ.regs.get64 r) → W s c) :
    XProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L 5 9 3 z2 4 Wk.wcPs J := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepA_pro (_root_.Executable.labels exe).label pc0 ⟨0, []⟩ σ Z L z2 (.inl rfl) hk r hr]
  · rintro s σ1 c _ _ _ _ _ _ ⟨σ, hJ, rfl⟩ k hk m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepA_pro (_root_.Executable.labels exe).label (xProN1 pc0 J).pc (xProN1 pc0 J).o (xS1 σ) Z L
      z2 (.inr (.inl rfl)) hk r hr, keepA_xS1 σ r hr]
  · rintro s c ⟨-, -, -, -, σ2, hA, -, σ, hJ, rfl⟩
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    rw [hA.regs, keepA_xS2 Z σ r hr]
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k hk m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepA_pro (_root_.Executable.labels exe).label (xProN3 ms pc0 5 9 Z lim J).pc
      (xProN3 ms pc0 5 9 Z lim J).o (xS3 Z (v.setWidth 64) σ) Z L z2 (.inr (.inr (.inl rfl))) hk r hr,
      keepA_xS3 Z _ σ r hr]
  · rintro s σ4 c _ _ _ _ _ _ ⟨σ, v, hJ, -, hreg, -⟩ k hk m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepA_pro (_root_.Executable.labels exe).label (xProN4 ms pc0 5 9 3 z2 Z lim J).pc
      (xProN4 ms pc0 5 9 3 z2 Z lim J).o σ4 Z L z2 (.inr (.inr (.inr rfl))) hk r hr,
      show σ4.regs.get64 r = _ from congrArg (·.get64 r) hreg, keepA_xS3 Z _ σ r hr]

end Pro

/-- `ArgR` is inhabited (non-vacuity). -/
example : ArgR .rdi := Or.inl rfl

/-- The thread worker's spills are `wc_worker`'s, so `xProW_args` serves both prologues. -/
example : thrPs = Wk.wcPs := rfl

end Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.xProW_args' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.xProW_args
