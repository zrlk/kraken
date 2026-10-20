/-
**WeakCore's Michael–Scott `deq` on x64,
hand-lowered under the x64 MS queue pilot's stackless register-link convention**
(`Lower/MsqXRProg.lean`: call `leaq ret(%rip), %r11; jmp f`, return `jmp
*%r11`, no stack, `dmem` empty; argument `rdi`; callee-saved `rbx rbp
r12–r15`; a `main` keeps its link in `rbp`).

WeakCore's `deqBody` (`WeakCore/CoreTerm.lean`, `queueLib`) differs from
msqueue2's `deq` (the x64 MS queue pilot's `deqFrag`):

- it **tries once**: `next = null` returns `inr ()`; only a failed `head`
  CAS retries;
- it has **no `head = tail` check** (so no `tail` read at all, and no
  helping swing of `tail`);
- it reads the payload **after** the successful `head` CAS.

`wdeqFrag` is the natural TSO lowering: `movq` loads, `lock cmpxchgq`. The
result is the wide sum `[tag, payload]`: `rax = 0` and the payload in `rdx`
for `inl`, `rax = 1` for `inr ()` (`rdx` then unspecified).

**Deviation (payload).** The x64 queue protocol (`EnvG/X64MsQueue2Ghost.lean`)
has no data word: a node's link is at `[n]`. So, as the x64 MS queue pilot does, the payload is
the new dummy node's pointer (`rcx`, already in a register): there is no load
after the CAS.

The enqueuer is the x64 MS queue pilot's unchanged (`MsqXR.fragE`). Two dequeuer shapes:

- `wcMsqX`: `main_w() { (r12, r13) := deq(&head); (r14, r15) := deq(&head) }`
  (one dequeuer calling twice, both results kept);
- `wcMsqX1`: `main_o() { (r12, r13) := deq(&head) }`, run by two threads (two
  dequeuers calling once each; explorer only).

**Evidence file: no Promising-level theorem.** `wdeq` does **not** fit the
x64 queue protocol `EnvG/X64MsQueue2*` (nor `X64MsQueue3*`, same `form`).
x64's `HeadF` (`X64MsQueue2Ghost.lean`) requires the swing's `tail` read
`yt ≠ z` with its windows, which `vc_d_pop` takes from `D3`'s `tail` read and
`hne` (`X64MsQueue2VC.lean`); `wdeq` reads no `tail`. Reachable
counterexample: the enqueuer links `n1` at `[s]` with `tail = s`; `wdeq` reads
`head = s`, `[s] = n1` and swings `head` to `n1`, when no `tail` message
`≠ s` exists. The same run breaks the final law's `HH` (`head` not ahead of
`tail`, `X64MsQueue2Final.lean`). The fix (an x64 `HeadFW` modelled on
AArch64's `MsQueue2Ghost.HeadF`: `v ≠ 0` plus a `[z]` link read, no `tail`;
`Hist` without `HH`; ≈1.7k new lines with the pilot) is deferred.
-/
import Kraken.Promising.Lower.MsqXRProg

namespace Kraken.Promising.Lower.WcMsqX

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.X64.Parser
open Kraken.Promising.Lower.MsqXR (fragE)

/-- **WeakCore's `deq`** (`deqBody`): `head` read, link read, `null` test,
`head` CAS (retry on failure), result `[tag, payload]` in `rax`/`rdx`. -/
def wdeqFrag : Program := parse("
wdeq:
    movq (%rdi), %rdx
    movq (%rdx), %rcx
    testq %rcx, %rcx
    je wdeq_empty
    movq %rdx, %rax
    lock cmpxchgq %rcx, (%rdi)
    jne wdeq
    xorl %eax, %eax
    movq %rcx, %rdx
    jmp *%r11
wdeq_empty:
    movl $1, %eax
    jmp *%r11
")

def mainWBody : Program := parse("
    movq %r11, %rbp
    movq %rbx, %rdi
    leaq ret_w1(%rip), %r11
    jmp wdeq
")
def retW1Body : Program := parse("
    movq %rax, %r12
    movq %rdx, %r13
    movq %rbx, %rdi
    leaq ret_w2(%rip), %r11
    jmp wdeq
")
def retW2Body : Program := parse("
    movq %rax, %r14
    movq %rdx, %r15
    jmp *%rbp
")

/-- `main_w`'s three blocks: two calls, both results kept. -/
def mainWTxt : Program :=
  .label "main_w" :: mainWBody ++ .label "ret_w1" :: retW1Body ++ .label "ret_w2" :: retW2Body

/-- The dequeuer's part of the text. -/
def fragW : Program := mainWTxt ++ wdeqFrag

/-- **The hand-lowered program** (one text: the x64 MS queue pilot's enqueuer, the try-once
dequeuer; no stack). -/
def wcMsqX : Program := fragE ++ fragW ++ [.label "done"]

/-- info: (61, 50, 26) -/
#guard_msgs in
#eval (wcMsqX.length, (wcMsqX.filter (!·.isLabel)).length,
  ((wcMsqX.takeWhile (· != .label "main_w")).filter (!·.isLabel)).length)

def mainOBody : Program := parse("
    movq %r11, %rbp
    movq %rbx, %rdi
    leaq ret_o(%rip), %r11
    jmp wdeq
")
def retOBody : Program := parse("
    movq %rax, %r12
    movq %rdx, %r13
    jmp *%rbp
")

/-- The one-shot dequeuer's `main_o`. -/
def mainOTxt : Program := .label "main_o" :: mainOBody ++ .label "ret_o" :: retOBody

/-- The two-dequeuer text (explorer only). -/
def wcMsqX1 : Program := fragE ++ (mainOTxt ++ wdeqFrag) ++ [.label "done"]

/-- info: (55, 45, 26) -/
#guard_msgs in
#eval (wcMsqX1.length, (wcMsqX1.filter (!·.isLabel)).length,
  ((wcMsqX1.takeWhile (· != .label "main_o")).filter (!·.isLabel)).length)

/-! ## Explorer runs (`Arch.tso`) -/

/-- The `.kl` runner's layout. -/
@[reducible] def wxLayout (p : Program) : _root_.Layout := Concrete.klLayout p 0x100000

/-- A thread of `p` at instruction `pc` with `rbx`/`r12`/`r13` set, link at
the end (`n` instructions). -/
def thr (p : Program) (n pc : Nat) (rbx r12 r13 : BitVec 64) : X64.State where
  exe := wxLayout p p
  endPc := 0x100000 + Int64.ofNat n
  st := ({ ({} : MachineData) with
    regs := (((({} : MachineData).regs.set64 .rbx rbx).set64 .r12 r12).set64 .r13 r13).set64 .r11
      (0x100000 + Int64.ofNat n).toBitVec }, 0x100000 + Int64.ofNat pc)

/-- msqueue2's initial memory: `head = tail = s`, the links zero. -/
def initMemW : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x2000), (⟨0x1008, 8⟩, 0x2000), (⟨0x2000, 8⟩, 0), (⟨0x2100, 8⟩, 0), (⟨0x2200, 8⟩, 0)]

/-- A result `(tag, payload)` read as `0` (`inr ()`) or the node. -/
def res (tag pay : BitVec 64) : Nat := if tag = 0 then pay.toNat else 0

/-- One dequeuer calling twice: its two results per final. -/
def exploreW (o : ExploreOpts) : List (Nat × Nat) × Bool × List String :=
  let r := explore Arch.tso (Config.init [thr wcMsqX 50 0 0x1008 0x2100 0x2200, thr wcMsqX 50 26 0x1000 0 0]
      initMemW : Config isa)
    (fun c => match c.threads.toList with
      | [_, d] => let g := d.st.st.1.regs.get64
        (res (g .r12) (g .r13), res (g .r14) (g .r15))
      | _ => (7, 7)) o
  (r.finals, r.boundHit, r.faults)

/-- **One dequeuer calling twice** (promise-free): the results are a prefix
of `n1 n2` padded by `inr ()` anywhere it may fall: `(empty, empty)`,
`(empty, n1)`, `(n1, empty)`, `(n1, n2)`; never `n2` before `n1`; no fault. -/
def wcRun0 : List (Nat × Nat) × Bool × List String := exploreW { fuel := 80, maxPromises := some 0 }

/-- info: ([(8448, 8704), (0, 0), (8448, 0), (0, 8448)], false, []) -/
#guard_msgs in
#eval wcRun0

/-- Two dequeuers calling once each: their two results per final. -/
def exploreO (o : ExploreOpts) : List (Nat × Nat) × Bool × List String :=
  let r := explore Arch.tso (Config.init [thr wcMsqX1 45 0 0x1008 0x2100 0x2200,
      thr wcMsqX1 45 26 0x1000 0 0, thr wcMsqX1 45 26 0x1000 0 0] initMemW : Config isa)
    (fun c => match c.threads.toList with
      | [_, d1, d2] => let g1 := d1.st.st.1.regs.get64; let g2 := d2.st.st.1.regs.get64
        (res (g1 .r12) (g1 .r13), res (g2 .r12) (g2 .r13))
      | _ => (7, 7)) o
  (r.finals, r.boundHit, r.faults)

/-- **The same with up to one promise per thread** (about 45 s): the same
four finals. -/
def wcRun1 : List (Nat × Nat) × Bool × List String := exploreW { fuel := 80, maxPromises := some 1 }

/-- info: ([(8448, 8704), (0, 0), (8448, 0), (0, 8448)], false, []) -/
#guard_msgs in
#eval wcRun1

/-- **Two dequeuers calling once each** (promise-free): `(n1, n2)`,
`(n2, n1)`, `(empty, empty)`, `(n1, empty)`, `(empty, n1)`; never `n2` while
the other dequeuer got nothing; no fault. -/
def wcRunO0 : List (Nat × Nat) × Bool × List String := exploreO { fuel := 80, maxPromises := some 0 }

/-- info: ([(8448, 8704), (8704, 8448), (0, 0), (8448, 0), (0, 8448)], false, []) -/
#guard_msgs in
#eval wcRunO0

/-! ## The static check of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- Every cell of `wcMsqX` is a phase-1 tree. -/
theorem wcMsqX_phase1FX [Executable.ValidLayout (layout wcMsqX)] : Phase1TreeFX (layout wcMsqX) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout fun d hd e z s pc => ?_)
  simp only [wcMsqX, fragE, fragW, MsqXR.mainETxt, MsqXR.enqFrag, mainWTxt, wdeqFrag, MsqXR.mainEBody,
    MsqXR.retE1Body, MsqXR.retE2Body, mainWBody, retW1Body, retW2Body, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.RelRegOrMem.interp]
  cells_phase1FX

end Static

end Kraken.Promising.Lower.WcMsqX
