/-
**hello.w on AArch64: main's state at its `clone`** (the pre-spawn half's interface): `ClonePreH`, wake's
`Spike.Lib.WakePreA.ClonePre` at hello's `wc_main`. It is the interface
between the one-thread consumer of main's code up to its `clone` (B3) and
the clone's row, error path and spawn (`ChildAt`/`ParentAt`, B4; the
spawn obligation, B8).

At main's `svc #0` (`.L22_wc_main.sp6` plus 25 instructions: `cloneAtH`,
`A64HelloWcSp6.wcNSH`) the one-slot configuration has one thread, at the
system call, asking for `clone(stack, tls)`:
- `stack = x1`, the child's stack top (the top of the second take's range
  `r1`);
- `tls = x3`, the child's TCB;
- `x9 .. x14` the worker's six argument words: the slice's four registers
  `sl0 .. sl3` (`wc_rodata`'s `x0 .. x3`: the buffer's address, `0`, `2`,
  `13`), the published cell `cA`, main's `ThreadId` word `meW`.

Every range held is held for index 0. Main's frame is `wc_main`'s 144 bytes
at `sp`, 224 bytes below `r0`'s top (`scc_rt_main`'s 80 and `wc_main`'s
144). The source thread is at `main`'s `spawn` (`HelloMainPreSrc.SpawnSrcH`:
`c`, `me`, `sl` and the packet `p` bound), the slice's words represented by
the four registers (`SlRep`). Rodata's buffer `⟨lb, 0⟩`, `⟨lb, 1⟩` (`lb` the
slice's label) has, in the source memory, latest messages holding `bufW 0`,
`bufW 1`, neither the last message (the box's `new` comes after): the
spawn's `FrzBufL` (`ClonePreH.frzBufL`).

The thread's promises are empty (`CertOkC`, as in wake).

- `cloneAtH`: the clone's pc in an executable, at `wc_main`'s label prefix.
- `bufW`: rodata's two buffer words (`Hello1RodataSrc.rdK1`, `rdK2`).
- `ClonePreH`: the interface. Its projections are `held`, `disj`,
  `frame`, `spTop`, `src`, `frz` and `frzBufL` (the spawn's `FrzBufL`).

**Producer.** The producer is `clonePreH_of`, from the segment's end
`ClonePostH` and the pre-spawn relation's facts. It is deferred: it waits
for source-run fact `helloSrc_frzL` for the `frz` conjunct.
-/
import Spike.Lib.WakePreA
import Spike.Lib.HelloMainPreSrc
import Spike.Lib.HelloFrz
import Spike.Lib.Hello1RodataSrc

namespace Spike.Lib.HelloPreA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64Consumer (Owned)
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH SlRep)

/-- **The clone's address**: the `svc #0` at `pfx ++ ".sp6"` plus 25
instructions (`A64HelloWcSp6`: eleven of the packet's copy, the fence,
thirteen of the arguments), in executable `exe`. -/
def cloneAtH (pfx : String) (exe : _root_.Executable) : Int64 :=
  (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25)

/-- **Rodata's buffer words** (the two lane stores of `wc_rodata`). -/
def bufW (i : Nat) : Nat := if i = 0 then Hello1RodataSrc.rdK1 else Hello1RodataSrc.rdK2

theorem bufW_zero : bufW 0 = Hello1RodataSrc.rdK1 := rfl

theorem bufW_one : bufW 1 = Hello1RodataSrc.rdK2 := rfl

/-- **main's state at its `clone`** in the one-slot configuration `t`, the
source configuration `s`, the source label placement `lbl`, `wc_main`'s
label prefix `pfx`, the layout `Λ`, main's stack range `r0`, the child's
`r1` and the runtime facts `X` of main's thread state there (see the module
docstring). There is one thread `th` and one source thread `th0`, at the
control `⟨th0.term, th0.env, hd⟩`.

Use the projections; the field order is not stable. -/
def ClonePreH (pfx : String) (Λ : Scc.Sem.Layout) (r0 r1 : Range) (X : State → Prop)
    (lbl : WeakMem.AllocLabel → Option Nat) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (tls cA meW : Nat)
    (sl0 sl1 sl2 sl3 : Nat) (l : WeakMem.AllocLabel) (ws : List TermRun.Word),
    t.1.threads = #[th] ∧ s.ths = #[th0] ∧
    th.st.st.2 = cloneAtH pfx th.st.exe ∧ abi.atSys th.st = true ∧ th.prom = [] ∧
    callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
    (th.st.st.1.regs.getXReg .X1).toNat = r1.lo + r1.size ∧ (th.st.st.1.regs.getXReg .X3).toNat = tls ∧
    (th.st.st.1.regs.getXReg .X9).toNat = sl0 ∧ (th.st.st.1.regs.getXReg .X10).toNat = sl1 ∧
    (th.st.st.1.regs.getXReg .X11).toNat = sl2 ∧ (th.st.st.1.regs.getXReg .X12).toNat = sl3 ∧
    (th.st.st.1.regs.getXReg .X13).toNat = cA ∧ (th.st.st.1.regs.getXReg .X14).toNat = meW ∧
    t.2.held = [(0, r1), (0, r0)] ∧ r1.Disjoint r0 ∧ Owned Λ r0 th.st ∧ Owned Λ r1 th.st ∧ X th.st ∧
    r0.lo ≤ th.st.st.1.regs.SP.toNat ∧ th.st.st.1.regs.SP.toNat + 144 ≤ r0.lo + r0.size ∧
    th.st.st.1.regs.SP.toNat + 224 = r0.lo + r0.size ∧ r0.size = 16384 ∧
    SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧ th0.tidLbl = some (mainTidLbl 2) ∧
    SlRep lbl ws sl0 sl1 sl2 sl3 ∧
    ValRep lbl (.loc ⟨l, 0⟩ 0) cA ∧ ValRep lbl (.loc ⟨mainTidLbl 2, 0⟩ 0) meW ∧
    ∀ lb, ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → ∀ i < 2, ∃ j m,
      SLatest s.mem ⟨lb, i⟩ j ∧ s.mem[j]? = some m ∧ m.val = .num (bufW i) ∧ j + 1 < s.mem.size

section Proj

variable {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **Every range held at the clone is main's**, one of them ending at the
child's stack top. -/
theorem ClonePreH.held (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    (∀ h ∈ t.2.held, h.1 = 0) ∧ (0, r1) ∈ t.2.held := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
  rw [hh]; simp

/-- **The child's stack range is off main's.** -/
theorem ClonePreH.disj (h : ClonePreH pfx Λ r0 r1 X lbl t s) : r1.Disjoint r0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdj, -⟩ := h
  exact hdj

/-- **main's frame is in its stack range** at the clone (`wc_main`'s 144
bytes at `sp`). -/
theorem ClonePreH.frame (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ r0.lo ≤ th.st.st.1.regs.SP.toNat ∧
      th.st.st.1.regs.SP.toNat + 144 ≤ r0.lo + r0.size := by
  obtain ⟨th, -, -, -, -, -, -, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlo, hfr,
    -⟩ := h
  exact ⟨th, ht, hlo, hfr⟩

/-- **main's `sp` at the clone is 224 bytes below its stack top**
(`scc_rt_main`'s 80 and `wc_main`'s 144), the stack range of 16 KiB. -/
theorem ClonePreH.spTop (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ th.st.st.1.regs.SP.toNat + 224 = r0.lo + r0.size ∧ r0.size = 16384 := by
  obtain ⟨th, -, -, -, -, -, -, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    htop, hsz, -⟩ := h
  exact ⟨th, ht, htop, hsz⟩

/-- **The source side at the clone**: main's source thread at `spawnTermH`
(`SpawnSrcH`), its id label main's, the slice's words at `x9 .. x12`
(`SlRep`), `c`'s label placed at `x13` and main's id at `x14`. -/
theorem ClonePreH.src (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (l : WeakMem.AllocLabel)
      (ws : List TermRun.Word), t.1.threads = #[th] ∧ s.ths = #[th0] ∧
      SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧ th0.tidLbl = some (mainTidLbl 2) ∧
      SlRep lbl ws (th.st.st.1.regs.getXReg .X9).toNat (th.st.st.1.regs.getXReg .X10).toNat
        (th.st.st.1.regs.getXReg .X11).toNat (th.st.st.1.regs.getXReg .X12).toNat ∧
      ValRep lbl (.loc ⟨l, 0⟩ 0) (th.st.st.1.regs.getXReg .X13).toNat ∧
      ValRep lbl (.loc ⟨mainTidLbl 2, 0⟩ 0) (th.st.st.1.regs.getXReg .X14).toNat := by
  obtain ⟨th, th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l, ws, ht, hs, -, -, -, -, -, -, h9, h10, h11, h12, h13,
    h14, -, -, -, -, -, -, -, -, -, hS, hT, hR, hc, hm, -⟩ := h
  subst h9 h10 h11 h12 h13 h14
  exact ⟨th, th0, hd, l, ws, ht, hs, hS, hT, hR, hc, hm⟩

/-- **Rodata's buffer at the clone**: in the source memory, the latest
messages to the slice's label's two words hold `bufW 0`, `bufW 1`, neither
the last message. -/
theorem ClonePreH.frz (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ (th0 : TermRun.TTh) (ws : List TermRun.Word) (lb : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "sl") = some (HelloMainPreSrc.slTy, ws) ∧
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) ∧ ∀ i < 2, ∃ j m,
        SLatest s.mem ⟨lb, i⟩ j ∧ s.mem[j]? = some m ∧ m.val = .num (bufW i) ∧ j + 1 < s.mem.size := by
  obtain ⟨th, th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l, ws, -, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hS, -, hR, -, -, hf⟩ := h
  obtain ⟨-, -, -, -, hsl, -⟩ := hS
  obtain ⟨lb, rfl, -⟩ := hR
  exact ⟨th0, _, lb, hs, hsl, rfl, hf lb rfl⟩

/-- **The spawn's `FrzBufL`** (`HelloFrz.frzBufL_start` at `S = s.mem.size`)
for the slice's buffer label. -/
theorem ClonePreH.frzBufL (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ lb : WeakMem.AllocLabel, (∃ th0 ws, s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "sl") = some (HelloMainPreSrc.slTy, ws) ∧
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0))) ∧ HelloFrz.FrzBufL s.mem.size lb bufW 2 s.mem := by
  obtain ⟨th0, ws, lb, hs, hsl, hh, hf⟩ := h.frz
  exact ⟨lb, ⟨th0, ws, hs, hsl, hh⟩, HelloFrz.frzBufL_start hf⟩

end Proj

/-- info: 'Spike.Lib.HelloPreA.ClonePreH.frzBufL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePreH.frzBufL

/-- info: 'Spike.Lib.HelloPreA.ClonePreH.src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePreH.src

end Spike.Lib.HelloPreA
