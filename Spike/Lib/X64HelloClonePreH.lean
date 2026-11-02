/-
**hello.w on x86-64: main's state at its `clone`** (the twin of `Spike/Lib/A64HelloClonePreH.lean`):
`ClonePreH`, x86-64 wake's `Spike.Lib.X64WakePreA.ClonePre` at hello's `wc_main`. It is the interface
between the one-thread consumer of main's code up to its `clone` and the clone's row, error path and spawn
(`ChildAt`/`ParentAt`; the spawn obligation).

At main's `syscall` (`.Lwc_main.x25 + 94`: `cloneAtH`, `X64HelloWcSp6.wcNSH`) the one-slot configuration has
one thread, at the system call, asking for `clone(stack, tls)`:
- `stack = %rsi`, the child's stack top (the top of the second take's range `r1`);
- `tls = %r8`, the child's TCB;
- `%r12, %rbx, %r13, %r14, %r15, %r9` the worker's six argument words: the slice's four registers
  `sl0 .. sl3` (`wc_rodata`'s returns: the buffer's address, `0`, `2`, `13`), the published cell `cA`, main's
  `ThreadId` word `meW`.

Every range held is held for index 0. Main's frame is `wc_main`'s 144 bytes at `%rsp` (the 128 below `%rbp`,
the saved `%rbp` and the return address), 224 bytes below `r0`'s top (`scc_rt_start`'s `call` into
`scc_rt_main`: 16 bytes and `subq $64`; its `call` into `wc_main`: 16 more and `subq $128`). The source thread
is at `main`'s `spawn` (`X64HelloMainPreSrc.SpawnSrcH`), the slice's words represented by the four registers
(`SlRep`). Rodata's buffer `⟨lb, 0⟩`, `⟨lb, 1⟩` (`lb` the slice's label) has, in the source memory, latest
messages holding `bufW 0`, `bufW 1`, neither the last message (`X64HelloInst.BufAtSpawn`): the spawn's
`FrzBufL` (`ClonePreH.frzBufL`).

The thread's promises are empty.

- `cloneAtH`: the clone's pc in an executable.
- `ClonePreH`: the interface. Its projections are `held`, `disj`, `frame`, `spTop`, `src`, `frz` and
  `frzBufL`.

## Differences from the AArch64 version

- The x86-64 labels are not numbered per program (`.Lwc_main.x25`), so `cloneAtH` and `ClonePreH` drop
  AArch64's label prefix `pfx` (as `X64WakePreA` does wake's).
- The clone's arguments are `%rsi`/`%r8` (AArch64: `x1`/`x3`); the worker's words are in
  `%r12, %rbx, %r13, %r14, %r15, %r9` (AArch64: `x9 .. x14`).
- `bufW` and `BufAtSpawn` are `X64HelloInst`'s (imported, not redefined); the buffer conjunct is stated with
  `BufAtSpawn` (AArch64 spells it out; the two are the same proposition).
-/
import Spike.Lib.X64WakePreA
import Spike.Lib.X64HelloMainPreSrc
import Spike.Lib.X64HelloInst
import Spike.Lib.X64HelloWcSp6
import Spike.Lib.HelloFrz

namespace Spike.Lib.X64HelloPreA

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64Consumer (Owned)
open Spike.Lib.X64WakeA64 (Cfg)
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64HelloInst (bufW BufAtSpawn)
open Spike.Lib.X64.HelloPh.WcSp6 (x25L)

/-- **The clone's address**: the `syscall` at `.Lwc_main.x25 + 94` (`X64HelloWcSp6.wcNSH`: the packet's copy,
the fence, the loads, the two zeroings and `movl $56`), in executable `exe`. -/
def cloneAtH (exe : _root_.Executable) : Int64 :=
  (_root_.Executable.labels exe).label x25L + 94

/-- **main's state at its `clone`** in the one-slot configuration `t`, the source configuration `s`, the
source label placement `lbl`, the layout `Λ`, main's stack range `r0`, the child's `r1` and the runtime facts
`X` of main's thread state there (see the module docstring). There is one thread `th` and one source thread
`th0`, at the control `⟨th0.term, th0.env, hd⟩`.

Use the projections; the field order is not stable. Its inhabitant is the instance's: `X64HelloHClW.hClH_of`
produces it from the pre-spawn segment's end (through `X64HelloClonePreHOf.clonePreH_of`). -/
def ClonePreH (Λ : Scc.Sem.Layout) (r0 r1 : Range) (X : State → Prop)
    (lbl : WeakMem.AllocLabel → Option Nat) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (tls cA meW : Nat)
    (sl0 sl1 sl2 sl3 : Nat) (l : WeakMem.AllocLabel) (ws : List TermRun.Word),
    t.1.threads = #[th] ∧ s.ths = #[th0] ∧
    th.st.st.2 = cloneAtH th.st.exe ∧ abi.atSys th.st = true ∧ th.prom = [] ∧
    callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
    (th.st.st.1.regs.get64 .rsi).toNat = r1.lo + r1.size ∧ (th.st.st.1.regs.get64 .r8).toNat = tls ∧
    (th.st.st.1.regs.get64 .r12).toNat = sl0 ∧ (th.st.st.1.regs.get64 .rbx).toNat = sl1 ∧
    (th.st.st.1.regs.get64 .r13).toNat = sl2 ∧ (th.st.st.1.regs.get64 .r14).toNat = sl3 ∧
    (th.st.st.1.regs.get64 .r15).toNat = cA ∧ (th.st.st.1.regs.get64 .r9).toNat = meW ∧
    t.2.held = [(0, r1), (0, r0)] ∧ r1.Disjoint r0 ∧ Owned Λ r0 th.st ∧ Owned Λ r1 th.st ∧ X th.st ∧
    r0.lo ≤ (th.st.st.1.regs.get64 .rsp).toNat ∧ (th.st.st.1.regs.get64 .rsp).toNat + 144 ≤ r0.lo + r0.size ∧
    (th.st.st.1.regs.get64 .rsp).toNat + 224 = r0.lo + r0.size ∧ r0.size = 16384 ∧
    SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧ th0.tidLbl = some (mainTidLbl 2) ∧
    SlRep lbl ws sl0 sl1 sl2 sl3 ∧
    ValRep lbl (.loc ⟨l, 0⟩ 0) cA ∧ ValRep lbl (.loc ⟨mainTidLbl 2, 0⟩ 0) meW ∧
    ∀ lb, ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb

section Proj

variable {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **Every range held at the clone is main's**, one of them ending at the child's stack top. -/
theorem ClonePreH.held (h : ClonePreH Λ r0 r1 X lbl t s) :
    (∀ h ∈ t.2.held, h.1 = 0) ∧ (0, r1) ∈ t.2.held := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
  rw [hh]; simp

/-- **The child's stack range is off main's.** -/
theorem ClonePreH.disj (h : ClonePreH Λ r0 r1 X lbl t s) : r1.Disjoint r0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdj, -⟩ := h
  exact hdj

/-- **main's frame is in its stack range** at the clone (`wc_main`'s 144 bytes at `%rsp`). -/
theorem ClonePreH.frame (h : ClonePreH Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ r0.lo ≤ (th.st.st.1.regs.get64 .rsp).toNat ∧
      (th.st.st.1.regs.get64 .rsp).toNat + 144 ≤ r0.lo + r0.size := by
  obtain ⟨th, -, -, -, -, -, -, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlo, hfr,
    -⟩ := h
  exact ⟨th, ht, hlo, hfr⟩

/-- **main's `%rsp` at the clone is 224 bytes below its stack top** (`scc_rt_main`'s 80 and `wc_main`'s 144),
the stack range of 16 KiB. -/
theorem ClonePreH.spTop (h : ClonePreH Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ (th.st.st.1.regs.get64 .rsp).toNat + 224 = r0.lo + r0.size ∧ r0.size = 16384 := by
  obtain ⟨th, -, -, -, -, -, -, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    htop, hsz, -⟩ := h
  exact ⟨th, ht, htop, hsz⟩

/-- **The source side at the clone**: main's source thread at `spawnTermH` (`SpawnSrcH`), its id label main's,
the slice's words at `%r12, %rbx, %r13, %r14` (`SlRep`), `c`'s label placed at `%r15` and main's id at `%r9`. -/
theorem ClonePreH.src (h : ClonePreH Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isa) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (l : WeakMem.AllocLabel)
      (ws : List TermRun.Word), t.1.threads = #[th] ∧ s.ths = #[th0] ∧
      SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧ th0.tidLbl = some (mainTidLbl 2) ∧
      SlRep lbl ws (th.st.st.1.regs.get64 .r12).toNat (th.st.st.1.regs.get64 .rbx).toNat
        (th.st.st.1.regs.get64 .r13).toNat (th.st.st.1.regs.get64 .r14).toNat ∧
      ValRep lbl (.loc ⟨l, 0⟩ 0) (th.st.st.1.regs.get64 .r15).toNat ∧
      ValRep lbl (.loc ⟨mainTidLbl 2, 0⟩ 0) (th.st.st.1.regs.get64 .r9).toNat := by
  obtain ⟨th, th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l, ws, ht, hs, -, -, -, -, -, -, h9, h10, h11, h12, h13,
    h14, -, -, -, -, -, -, -, -, -, hS, hT, hR, hc, hm, -⟩ := h
  subst h9 h10 h11 h12 h13 h14
  exact ⟨th, th0, hd, l, ws, ht, hs, hS, hT, hR, hc, hm⟩

/-- **Rodata's buffer at the clone**: in the source memory, the latest messages to the slice's label's two
words hold `bufW 0`, `bufW 1`, neither the last message. -/
theorem ClonePreH.frz (h : ClonePreH Λ r0 r1 X lbl t s) :
    ∃ (th0 : TermRun.TTh) (ws : List TermRun.Word) (lb : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "sl") = some (X64HelloSplit.slTy, ws) ∧
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) ∧ ∀ i < 2, ∃ j m,
        SLatest s.mem ⟨lb, i⟩ j ∧ s.mem[j]? = some m ∧ m.val = .num (bufW i) ∧ j + 1 < s.mem.size := by
  obtain ⟨th, th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l, ws, -, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hS, -, hR, -, -, hf⟩ := h
  obtain ⟨-, -, -, -, hsl, -⟩ := hS
  obtain ⟨lb, rfl, -⟩ := hR
  exact ⟨th0, _, lb, hs, hsl, rfl, hf lb rfl⟩

/-- **The spawn's `FrzBufL`** (`HelloFrz.frzBufL_start` at `S = s.mem.size`) for the slice's buffer label. -/
theorem ClonePreH.frzBufL (h : ClonePreH Λ r0 r1 X lbl t s) :
    ∃ lb : WeakMem.AllocLabel, (∃ th0 ws, s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "sl") = some (X64HelloSplit.slTy, ws) ∧
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0))) ∧ HelloFrz.FrzBufL s.mem.size lb bufW 2 s.mem := by
  obtain ⟨th0, ws, lb, hs, hsl, hh, hf⟩ := h.frz
  exact ⟨lb, ⟨th0, ws, hs, hsl, hh⟩, HelloFrz.frzBufL_start hf⟩

end Proj

/-- info: 'Spike.Lib.X64HelloPreA.ClonePreH.frzBufL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePreH.frzBufL

/-- info: 'Spike.Lib.X64HelloPreA.ClonePreH.src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePreH.src

end Spike.Lib.X64HelloPreA
