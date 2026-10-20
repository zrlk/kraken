/-
**Part 1: `msqueue2.kl` hand-lowered to functions**
under the first lowering pilot's frameless convention.

The enqueuer and the dequeuer of `Kraken/Examples/LockFree/AArch64/msqueue2.kl`
(`enq2Prog`/`deq2Prog`, `EnvG/MsQueue2Smoke.lean`) rewritten as what the
WeakCore lowering would emit for

```
main_e() { n1.v := 1; enq(&q, n1); n2.v := 2; enq(&q, n2) }
main_d() { r1 := deq(&q); r2 := deq(&q); res := (r1, r2) }
```

- `enq(x0 = q, x1 = node)` (leaf): `q` points to the queue's words,
  `head` at `[q]` and `tail` at `[q + 8]`; the node goes to `x2`, `&tail` to
  `x1`, then msqueue2's loop verbatim (`ldar` of `tail` and of the link,
  helping `casal` of `tail`, link `casal`, swing `casal`); the swing returns by
  `ret` in place of `b enq1_end`.
- `deq(x0 = q) → x0` (leaf): msqueue2's dequeue loop verbatim (behind
  `add x1, x0, #8`, recomputed at each retry), returns the data word read from
  the dequeued node (`mov w0, w7`) by `ret` in place of `mov w10, w7`.
- `main_e`/`main_d` (non-leaf; the first lowering pilot deviation 1): the link `x30` saved in the
  callee-saved `x19`; `q` in the callee-saved `x21`, the statically allocated
  nodes `n1`/`n2` in the callee-saved `x22`/`x23` (msqueue2's `x12`/`x13`,
  moved to callee-saved registers because they live across calls);
  `main_e` stores each node's data word before its `enq` (`str w9, [x22]`, the
  initial store of `new`, as the first lowering pilot's `main`); `main_d` keeps the first result
  in the callee-saved `x20` across the second call and leaves the results in
  `x10`/`x11` (the first lowering pilot deviation 2, the `.kl`'s registers).
- The nodes are static (msqueue2's `n1`, `n2`), not bump-allocated: this pilot
  is about the call/return lowering of a CAS-loop structure; the first lowering pilot covers the
  bump allocator.
- Each thread has its own text (its `main` and the function it calls), as
  `msqueue2_envG` has its own layout per thread; the trailing label gives
  `not_instrStepEnv_of_end_labels _ 1`.

Contents: the programs, the runner-style layouts, the start states, the
explorer run (`#guard_msgs`), the static checks of the EnvG link.
-/
import Kraken.Promising.SLR.EnvG.MsQueue2Public
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.Lower.MsqPilot

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-! ## The pieces

`main_e`/`main_d` are single blocks: a straight-line prefix, `bl`, a
straight-line middle, `bl`, a straight-line tail ending in `ret`. The pieces
are named so that `Lower/MsqPilotMain.lean` can follow them with
`PartialWpEnv.of_wpEnv`/`PartialWpEnv.call`. -/

/-- `bl l`. -/
abbrev blTo (l : Label) : Directive := Directive.instr ⟨.W64, .BL (.label l)⟩

/-- `main_e` up to the first `bl enq`: save the link, store `n1`'s data word,
the arguments `q`, `n1`. -/
def ePre : Program := parseAArch64("
    mov x19, x30
    mov w9, #1
    str w9, [x22]
    mov x0, x21
    mov x1, x22
")

/-- Between the `bl enq`s: store `n2`'s data word, the arguments `q`, `n2`. -/
def eMid : Program := parseAArch64("
    mov w9, #2
    str w9, [x23]
    mov x0, x21
    mov x1, x23
")

/-- Behind the second `bl enq`: restore the link, return. -/
def eTail : Program := parseAArch64("
    mov x30, x19
    ret
")

/-- `main_e`'s block. -/
def mainEBody : Program := ePre ++ blTo "enq" :: (eMid ++ blTo "enq" :: (eTail ++ []))

/-- **`enq(x0 = q, x1 = node)`**: msqueue2's enqueue loop. -/
def enqFrag : Program := parseAArch64("
enq:
    mov x2, x1
    add x1, x0, #8
enq_loop:
    ldar x3, [x1]
    add x8, x3, #8
    ldar x4, [x8]
    cbnz x4, enq_fix
    mov x5, #0
    casal x5, x2, [x8]
    cbnz x5, enq_loop
    mov x5, x3
    casal x5, x2, [x1]
    ret
enq_fix:
    mov x5, x3
    casal x5, x4, [x1]
    b enq_loop
")

/-- **The enqueuer's text**: `main_e`, then `enq`. -/
def progE : Program := parseAArch64("
main_e:
    mov x19, x30
    mov w9, #1
    str w9, [x22]
    mov x0, x21
    mov x1, x22
    bl enq
    mov w9, #2
    str w9, [x23]
    mov x0, x21
    mov x1, x23
    bl enq
    mov x30, x19
    ret
enq:
    mov x2, x1
    add x1, x0, #8
enq_loop:
    ldar x3, [x1]
    add x8, x3, #8
    ldar x4, [x8]
    cbnz x4, enq_fix
    mov x5, #0
    casal x5, x2, [x8]
    cbnz x5, enq_loop
    mov x5, x3
    casal x5, x2, [x1]
    ret
enq_fix:
    mov x5, x3
    casal x5, x4, [x1]
    b enq_loop
e_end:
")

/-- `progE` is its pieces. -/
theorem progE_split : progE = (Directive.label "main_e" :: mainEBody) ++ enqFrag ++ [Directive.label "e_end"] := by
  decide

/-- `main_d` up to the first `bl deq`. -/
def dPre : Program := parseAArch64("
    mov x19, x30
    mov x0, x21
")

/-- Between the `bl deq`s: keep the first result in the callee-saved `x20`. -/
def dMid : Program := parseAArch64("
    mov x20, x0
    mov x0, x21
")

/-- Behind the second `bl deq`: the results to `x10`/`x11`, return. -/
def dTail : Program := parseAArch64("
    mov x10, x20
    mov x11, x0
    mov x30, x19
    ret
")

/-- `main_d`'s block. -/
def mainDBody : Program := dPre ++ blTo "deq" :: (dMid ++ blTo "deq" :: (dTail ++ []))

/-- **`deq(x0 = q) → x0`**: msqueue2's dequeue loop. -/
def deqFrag : Program := parseAArch64("
deq:
    add x1, x0, #8
    ldar x3, [x0]
    ldar x4, [x1]
    add x8, x3, #8
    ldar x5, [x8]
    cmp x3, x4
    b.ne deq_ne
    cbz x5, deq
    mov x6, x3
    casal x6, x5, [x1]
    b deq
deq_ne:
    cbz x5, deq
    ldr w7, [x5]
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq
    mov w0, w7
    ret
")

/-- **The dequeuer's text**: `main_d`, then `deq`. -/
def progD : Program := parseAArch64("
main_d:
    mov x19, x30
    mov x0, x21
    bl deq
    mov x20, x0
    mov x0, x21
    bl deq
    mov x10, x20
    mov x11, x0
    mov x30, x19
    ret
deq:
    add x1, x0, #8
    ldar x3, [x0]
    ldar x4, [x1]
    add x8, x3, #8
    ldar x5, [x8]
    cmp x3, x4
    b.ne deq_ne
    cbz x5, deq
    mov x6, x3
    casal x6, x5, [x1]
    b deq
deq_ne:
    cbz x5, deq
    ldr w7, [x5]
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq
    mov w0, w7
    ret
d_end:
")

/-- `progD` is its pieces. -/
theorem progD_split : progD = (Directive.label "main_d" :: mainDBody) ++ deqFrag ++ [Directive.label "d_end"] := by
  decide

/-- info: (33, 33) -/
#guard_msgs in
#eval (progE.length, progD.length)

/-! ## Runner-style layouts and the start states -/

/-- The enqueuer's text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layoutE : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize progE
/-- The dequeuer's text at `0x200000`. -/
@[reducible] def layoutD : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize progD

instance validE : Executable.ValidLayout (layoutE progE) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)
instance validD : Executable.ValidLayout (layoutD progD) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- Thread `0`: `x21 = q = &head` (`0x1000`, `tail` at `0x1008`), `x22 = n1`,
`x23 = n2`, `x30 =` the end of the text (the runtime "calls" `main_e`); empty
private memory. -/
def threadE : AArch64.State where
  exe := layoutE progE
  endPc := 0x100000 + 4 * 28
  st := ({ regs := { X21 := 0x1000, X22 := 0x1200, X23 := 0x1300, X30 := 0x100000 + 4 * 28 } }, 0x100000)

/-- Thread `1`: `x21 = q`, `x30 =` the end of the text. -/
def threadD : AArch64.State where
  exe := layoutD progD
  endPc := 0x200000 + 4 * 29
  st := ({ regs := { X21 := 0x1000, X30 := 0x200000 + 4 * 29 } }, 0x200000)

/-- msqueue2's initial memory (`ConcreteMsQueue2.msqueue2InitMem`): `head = tail = d`, the links `0`. -/
def initMem : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1008, 8⟩, 0x1100), (⟨0x1108, 8⟩, 0), (⟨0x1208, 8⟩, 0), (⟨0x1308, 8⟩, 0)]

/-- The explorer: per final configuration, the dequeuer's `(x10, x11)`. -/
def exploreFinals (o : ExploreOpts) : List (Nat × Nat) × Bool × List String :=
  let r := explore Arch.armv8 (Config.init [threadE, threadD] initMem : Config isa)
    (fun c => match c.threads.toList with
      | [_, d] => (d.st.st.1.regs.X10.toBitVec.toNat, d.st.st.1.regs.X11.toBitVec.toNat)
      | _ => (0, 0)) o
  (r.finals, r.boundHit, r.faults)

/-- **The lowered program terminates with msqueue2's verdict** (`isa`,
promise-free exploration, `boundHit = false`: the promise-free state space is
exhausted within the fuel): every final configuration has the dequeuer's
`x10 = 1`, `x11 = 2`; no fault. Promise-free is an under-approximation of
the Promising machine; the Promising-level guarantee is `msqPilot_promising`. -/
def msqPilotRun : List (Nat × Nat) × Bool × List String :=
  exploreFinals { fuel := 60, maxPromises := some 0 }

/-- info: ([(1, 2)], false, []) -/
#guard_msgs in
#eval msqPilotRun

/-- **The same with at most one outstanding promise per thread** (`boundHit =
true`: the promise bound cuts the search): the same single final. About a
minute. -/
def msqPilotRun1 : List (Nat × Nat) × Bool × List String :=
  exploreFinals { fuel := 60, maxPromises := some 1 }

/-- info: ([(1, 2)], true, []) -/
#guard_msgs in
#eval msqPilotRun1

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

theorem progE_rmwLive : (layout progE).rmwLive = true := by rw [Layout.apply_rmwLive]; decide
theorem progD_rmwLive : (layout progD).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem progE_phase1F [Executable.ValidLayout (layout progE)] : Phase1TreeF (layout progE) :=
  phase1TreeF_of_dirs (by dirs_phase1F progE)
theorem progD_phase1F [Executable.ValidLayout (layout progD)] : Phase1TreeF (layout progD) :=
  phase1TreeF_of_dirs (by dirs_phase1F progD)

theorem progE_noFault : DirsNoFault (layout progE) := by dirs_no_fault' progE
theorem progD_noFault : DirsNoFault (layout progD) := by dirs_no_fault' progD

end Static

end Kraken.Promising.Lower.MsqPilot
