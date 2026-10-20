/-
**The Michael–Scott queue pilot with a
bump-allocating enqueuer.** ISA: AArch64.

The MS queue pilot (`Lower/MsqPilotProg.lean`) with the static nodes replaced by
the allocation pilot's allocator:

```
main_e() { n1 := new {1, null}; enq(&q, n1); n2 := new {2, null}; enq(&q, n2) }
main_d() { r1 := deq(&q); r2 := deq(&q); res := (r1, r2) }
```

- `main_e` saves `x30` in `x19`; `bl alloc` (`x0 := x27; x27 += 16`, limit
  `x28`); the data word's initial store `str w9, [x0]`; `enq(x0 = q, x1 = n)`;
  the same for the second node. `x27`/`x28` survive `enq` (callee-saved), so
  the two calls return `base` and `base + 16` (`Arena.alloc_chain`).
- **Emitter rule (zero fields, pre-zeroed arena).** WeakCore's `new` lowers a
  `null`/zero initial field to **no store**: the arena is fresh, pre-zeroed
  memory, and nodes are never reused (ABA and reuse are out of scope). Only
  the data word is stored. The reason is the protocol: in MsQueue2
  (`EnvG/MsQueue2Ghost.lean`) a node's link `[n + 8]` is a queue word
  (`Params2.IsL`), and `form2` admits a non-initial link message only of value
  `n1`/`n2` written by the enqueuer's link `casal` (`LinkF`); the allocation pilot's
  `str xzr, [x0, #8]` would add a link message of value `0`, which `form2`
  rejects. This matches WeakCore only under option A′ (WeakCore's `new`
  treats zeroable fields as `newBuf` does: zero messages, no stores; today
  `TermRun.alloc` performs every initial store, `null` fields included), or
  with a non-monotone timestamp map in the simulation's memory relation.
  The start hypothesis is MsQueue2's `InitV2` at `n1 = base`,
  `n2 = base + 16` (the two links `0`, `head = tail = d`, `d`'s link `0`);
  the data words may hold garbage.
- `enq`, `deq`, `alloc`: **verbatim** (`msqA_split`, `msqA_enq`, `msqA_alloc`:
  The MS queue pilot's `enqFrag`, the allocation pilot's `allocFrag`). The dequeuer's text is
  the MS queue pilot's `progD`, unchanged.

Contents: the enqueuer's text, the identity checks, the runner layout, the
explorer configuration, the static checks of the EnvG link,
`msqA_wcLowerable`.
-/
import Kraken.Promising.Lower.FragSpecMsq
import Kraken.Promising.Lower.FragSpecClients
import Kraken.Promising.Lower.LowerablePilots

namespace Kraken.Promising.Lower.MsqAlloc

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser
open Kraken.Promising.Lower.MsqPilot (blTo enqFrag progE progD)
open Kraken.Promising.Lower.Alloc (allocP allocFrag)

/-! ## The pieces of `main_e` -/

/-- The link save. -/
def aSave : Program := parseAArch64("
    mov x19, x30
")

/-- Behind the first `bl alloc`: node 1's data word, `enq`'s arguments. -/
def aInit1 : Program := parseAArch64("
    mov w9, #1
    str w9, [x0]
    mov x1, x0
    mov x0, x21
")

/-- Behind the second `bl alloc`: node 2's data word, `enq`'s arguments. -/
def aInit2 : Program := parseAArch64("
    mov w9, #2
    str w9, [x0]
    mov x1, x0
    mov x0, x21
")

/-- Behind the second `bl enq`: restore the link, return. -/
def aTail : Program := parseAArch64("
    mov x30, x19
    ret
")

/-- `main_e`'s block. -/
def mainABody : Program :=
  aSave ++ blTo "alloc" :: (aInit1 ++ blTo "enq" :: (blTo "alloc" :: (aInit2 ++ blTo "enq" :: (aTail ++ []))))

/-- **The enqueuer's text**: `main_e`, then the MS queue pilot's `enq` and the allocation pilot's
`alloc`, verbatim. -/
def msqA : Program := parseAArch64("
main_e:
    mov x19, x30
    bl alloc
    mov w9, #1
    str w9, [x0]
    mov x1, x0
    mov x0, x21
    bl enq
    bl alloc
    mov w9, #2
    str w9, [x0]
    mov x1, x0
    mov x0, x21
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
alloc:
    mov x0, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi alloc_oom
    ret
alloc_oom:
    b alloc_oom
e_end:
")

/-- **`msqA` is `main_e`, then the existing fragments** `MsqPilot.enqFrag` and
`Alloc.allocFrag`, verbatim. -/
theorem msqA_split :
    msqA = (Directive.label "main_e" :: mainABody) ++ enqFrag ++ allocFrag ++ [Directive.label "e_end"] := by
  decide +kernel

/-- **`enq` is the MS queue pilot's, unchanged**: the text from `enq:` agrees with
`progE`'s for `enq`'s length. -/
theorem msqA_enq : (Program.fromLabel msqA "enq").take enqFrag.length =
    (Program.fromLabel progE "enq").take enqFrag.length := by
  decide +kernel

/-- **`alloc` is the allocation pilot's, unchanged**: the text from `alloc:` agrees with
`allocP`'s for `alloc`'s length. -/
theorem msqA_alloc : (Program.fromLabel msqA "alloc").take allocFrag.length =
    (Program.fromLabel allocP "alloc").take allocFrag.length := by
  decide +kernel

/-- **`msqA` is WeakCore-lowerable** (`Lower/Lowerable.lean`). -/
theorem msqA_wcLowerable : Program.WCLowerable msqA := by decide

/-- The LSE2 route's `hfree`. -/
theorem msqA_lse2Free : ∀ d ∈ msqA, d.LSE2Free := msqA_wcLowerable.lse2Free

/-! ## Runner layout and the explorer configuration -/

/-- The enqueuer's text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layoutA : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize msqA

instance validA : Executable.ValidLayout (layoutA msqA) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The end address: `36` instructions of `4` bytes. -/
def endA : Int64 := 0x100000 + 144

/-- info: true -/
#guard_msgs in
#eval decide ((layoutA msqA).addrOf msqA.length = endA)

/-- Thread `0`: `x21 = q = &head` (`0x1000`), the arena `[0x2000, 0x2100)`
in `x27`/`x28`, `x30 =` the end of the text. -/
def threadA : AArch64.State where
  exe := layoutA msqA
  endPc := endA
  st := ({ regs := { X21 := 0x1000, X27 := 0x2000, X28 := 0x2100, X30 := 0x100000 + 144 } }, 0x100000)

/-- msqueue2's queue words (`head = tail = 0x1100`, its link `0`), the
pre-zeroed arena's links `0` and its data words garbage (`7`). -/
def initMemA : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1008, 8⟩, 0x1100), (⟨0x1108, 8⟩, 0), (⟨0x2008, 8⟩, 0), (⟨0x2018, 8⟩, 0),
    (⟨0x2000, 4⟩, 7), (⟨0x2010, 4⟩, 7)]

/-- The explorer: per final configuration, the dequeuer's `(x10, x11)` and
the enqueuer's `x27`. -/
def exploreFinals (o : ExploreOpts) : List (Nat × Nat × Nat) × Bool × List String :=
  let r := explore Arch.armv8 (Config.init [threadA, MsqPilot.threadD] initMemA : Config isa)
    (fun c => match c.threads.toList with
      | [e, d] => (d.st.st.1.regs.X10.toBitVec.toNat, d.st.st.1.regs.X11.toBitVec.toNat,
          e.st.st.1.regs.X27.toBitVec.toNat)
      | _ => (0, 0, 0)) o
  (r.finals, r.boundHit, r.faults)

/-- **The lowered program terminates with msqueue2's verdict** (`isa`,
promise-free exploration, `boundHit = false`: the promise-free state space is
exhausted within the fuel): every final configuration has the dequeuer's
`x10 = 1`, `x11 = 2`, the enqueuer's bump pointer past both nodes
(`0x2020`); no fault. Promise-free is an under-approximation of the Promising
machine; the Promising-level guarantee is `msqAlloc_promising`. About 15 s. -/
def msqAllocRun : List (Nat × Nat × Nat) × Bool × List String :=
  exploreFinals { fuel := 70, maxPromises := some 0 }

/-- info: ([(1, 2, 8224)], false, []) -/
#guard_msgs in
#eval msqAllocRun

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

theorem msqA_rmwLive : (layout msqA).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem msqA_phase1F [Executable.ValidLayout (layout msqA)] : Phase1TreeF (layout msqA) :=
  phase1TreeF_of_dirs (by dirs_phase1F msqA)

theorem msqA_noFault : DirsNoFault (layout msqA) := by dirs_no_fault' msqA

end Static

end Kraken.Promising.Lower.MsqAlloc
