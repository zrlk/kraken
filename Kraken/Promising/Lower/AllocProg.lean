/-
**A lowering pilot with client-side node
allocation.** WeakCore lowers `new {v, null}` to bump
allocation plus initial stores. Here
`main(v) { n := new {v, null}; push(&top, n); r := pop(&top); if r ≠ null then res := r.v }`
allocates by a call to the runtime leaf `alloc` and initialises inline:
- `alloc`: `x0 := x27; x27 += 16`, limit `x28` (`b.hi alloc_oom` spins: no
  halting instruction). `x27`/`x28` are the allocator's registers: callee-saved
  for everybody except `alloc`. No memory access.
- `main`: saves `x30` in `x19`; `bl alloc`; plain initial stores
  `str w20, [x0]` (payload, 4 bytes; `x20` callee-saved, it survives the call)
  and `str xzr, [x0, #8]` (link `null`); `push(x21 = &top, node)`; `pop`; keeps
  a non-null result in `x10`, its payload in `w11`.
- `push`, `pop`: the first lowering pilot's (`Lower/PilotProg.lean`); `pop` returns `0` on empty.
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.Lower.Alloc

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- **The hand-lowered program** (one text, four functions). -/
def allocP : Program := parseAArch64("
main:
    mov x19, x30
    bl alloc
    str w20, [x0]
    str xzr, [x0, #8]
    mov x1, x0
    mov x0, x21
    bl push
    mov x0, x21
    bl pop
ret_pop:
    cbz x0, empty
    mov x10, x0
    ldr w11, [x10]
empty:
    mov x30, x19
    ret
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

/-- info: 45 -/
#guard_msgs in
#eval allocP.length

/-- Text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def aLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize allocP

instance aValid : Executable.ValidLayout (aLayout allocP) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The end address: `36` instructions of `4` bytes. -/
def endA : Int64 := 0x100000 + 144

/-- Thread start: `x21 = &top`, arena `[x27, x28)`, payload `x20 = v`. -/
def thread (base v : UInt64) : AArch64.State where
  exe := aLayout allocP
  endPc := endA
  st := ({ regs := { X21 := 0x1000, X27 := base, X28 := base + 0x100, X20 := v, X30 := 0x100000 + 144 } },
    0x100000)

/-- Only `top = 0` is initialised: the arenas' words are garbage (`7`). -/
def initMem : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0), (⟨0x2000, 4⟩, 7), (⟨0x2008, 8⟩, 7), (⟨0x3000, 4⟩, 7), (⟨0x3008, 8⟩, 7)]

/-- The explorer: per final configuration, each thread's `(x10, w11, x27)`.
Not run in the build (3.7 min):
`exploreFinals { fuel := 40, maxPromises := some 0 }` =
`([[(8192, 1, 8208), (12288, 2, 12304)], [(12288, 2, 8208), (8192, 1, 12304)]], false, [])`:
each thread pops a pushed node with its owner's payload (never the garbage
`7`, never `0`), no fault. With one promise: not finished in 15 min. -/
def exploreFinals (o : ExploreOpts) : List (List (Nat × Nat × Nat)) × Bool × List String :=
  let proj := fun (ts : List AArch64.State) => ts.map fun s =>
      (s.st.1.regs.X10.toBitVec.toNat, s.st.1.regs.X11.toBitVec.toNat, s.st.1.regs.X27.toBitVec.toNat)
  let r := explore Arch.armv8 (Config.init [thread 0x2000 1, thread 0x3000 2] initMem : Config isa)
    (fun c => proj (c.threads.toList.map (·.st))) o
  (r.finals, r.boundHit, r.faults)

variable [layout : _root_.Layout]

theorem allocP_rmwLive : (layout allocP).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem allocP_phase1F [Executable.ValidLayout (layout allocP)] : Phase1TreeF (layout allocP) :=
  phase1TreeF_of_dirs (by dirs_phase1F allocP)

theorem allocP_noFault : DirsNoFault (layout allocP) := by dirs_no_fault' allocP

end Kraken.Promising.Lower.Alloc
