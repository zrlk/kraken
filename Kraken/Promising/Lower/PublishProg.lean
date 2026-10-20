/-
**The allocation pilot's client with WeakCore's `publish`
barrier in `push`.** ISA: AArch64.

WeakCore's Treiber push is `publish n; … cas rel top`, and `publish` (like
`intoRgn`, `region`) is a store fence `TermRun.fenceS s .st`, lowered to
`dmb ishst` on AArch64. It sits
after `new`'s initial stores and before the link CAS loop. Every earlier
pilot published through the `casal` alone. `publishP` is the allocation pilot's `allocP`
(`Lower/AllocProg.lean`) with `main` calling `pushp` instead of `push`:

- `pushp: dmb ishst; b push`: the barrier once, then a tail call into the
  existing CAS loop. The explicit `b push` keeps the first lowering pilot's `push` fragment
  (`Pilot.pushFrag`) verbatim, so its fragment specification
  `Pilot.pushFrag_spec` is reused, not re-proved (`FragSpecEnvL.tail`).
- `alloc`, `push`, `pop`: the allocation pilot's text, unchanged (`publishP_funs`).

Also `rmwLive`/`Phase1TreeF`/`DirsNoFault`, `publishP_wcLowerable`.
-/
import Kraken.Promising.Lower.FragSpecClients
import Kraken.Promising.Lower.LowerablePilots

namespace Kraken.Promising.Lower.Publish

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser
open Kraken.Promising.Lower.Alloc (allocP)

/-- **The hand-lowered program**: the allocation pilot's `main` calling `pushp`, the
publishing entry `pushp`, then the allocation pilot's `alloc`, `push` and `pop` verbatim. -/
def publishP : Program := parseAArch64("
main:
    mov x19, x30
    bl alloc
    str w20, [x0]
    str xzr, [x0, #8]
    mov x1, x0
    mov x0, x21
    bl pushp
    mov x0, x21
    bl pop
ret_pop:
    cbz x0, empty
    mov x10, x0
    ldr w11, [x10]
empty:
    mov x30, x19
    ret
pushp:
    dmb ishst
    b push
alloc:
    mov x0, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi alloc_oom
    ret
alloc_oom:
    b alloc_oom
push:
    ldar x2, [x0]
    str x2, [x1, #8]
    mov x3, x2
    casal x3, x1, [x0]
    cmp x3, x2
    b.ne push
    ret
pop:
    ldar x2, [x0]
    cbz x2, pop_done
    ldr x4, [x2, #8]
    mov x3, x2
    casal x3, x4, [x0]
    cmp x3, x2
    b.ne pop
pop_done:
    mov x0, x2
    ret
done:
")

/-- info: 48 -/
#guard_msgs in
#eval publishP.length

/-- **`alloc`, `push` and `pop` are the allocation pilot's, unchanged**: from `alloc:` on
the two texts are equal. -/
theorem publishP_funs : Program.fromLabel publishP "alloc" = Program.fromLabel allocP "alloc" := by
  decide +kernel

/-- **`publishP` is WeakCore-lowerable** (`Lower/Lowerable.lean`). -/
theorem publishP_wcLowerable : Program.WCLowerable publishP := by decide

/-- The LSE2 route's `hfree`. -/
theorem publishP_lse2Free : ∀ d ∈ publishP, d.LSE2Free := publishP_wcLowerable.lse2Free

variable [layout : _root_.Layout]

theorem publishP_rmwLive : (layout publishP).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem publishP_phase1F [Executable.ValidLayout (layout publishP)] : Phase1TreeF (layout publishP) :=
  phase1TreeF_of_dirs (by dirs_phase1F publishP)

theorem publishP_noFault : DirsNoFault (layout publishP) := by dirs_no_fault' publishP

end Kraken.Promising.Lower.Publish
