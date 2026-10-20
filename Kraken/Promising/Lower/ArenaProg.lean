/-
**A lowering pilot with two bump allocations per
thread.** WeakCore's Treiber clients allocate one node per
push (`new {v, null}`). Here
`main(v1, v2) { n1 := new {v1, null}; push(&top, n1); n2 := new {v2, null}; push(&top, n2); r := pop(&top); if r ≠ null then res := r.v }`
calls the allocation pilot's runtime leaf `alloc` twice:
- `alloc`, `push`, `pop`: **The allocation pilot's text, unchanged** (`allocP`'s functions,
  `arenaP_funs`: the two texts agree from `alloc:` on).
- `main`: saves `x30` in `x19`; `bl alloc`; the initial stores of node 1
  (`str w20, [x0]`, `str xzr, [x0, #8]`); `push`; `bl alloc` (the bump pointer
  `x27` survives `push`, which keeps `x19`–`x28`); the initial stores of node 2
  with the second payload `w22`; `push`; `pop`; keeps a non-null result in
  `x10`, its payload in `w11`.

Here: the program, its layout, the explorer driver, `rmwLive`/`Phase1TreeF`/
`DirsNoFault`, and `arenaP_wcLowerable`. The purity proof is
`Lower/ArenaPure.lean`. **No `arena_promising`**: no EnvG protocol of
`top` lets a thread push more than one node (`Treiber2.split` gives node `w`
at the first push and the pop token at every later write; `Treiber2Final`
counts one push-form message per thread). See `Lower/StackHistory.lean` for
the protocol-generic history law a `k`-node protocol would use.
-/
import Kraken.Promising.Lower.FragSpecClients
import Kraken.Promising.Lower.LowerablePilots

namespace Kraken.Promising.Lower.Arena

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser
open Kraken.Promising.Lower.Alloc (allocP)

/-- **The hand-lowered program**: a new `main`, then the allocation pilot's `alloc`, `push`
and `pop` verbatim. -/
def arenaP : Program := parseAArch64("
main:
    mov x19, x30
    bl alloc
    str w20, [x0]
    str xzr, [x0, #8]
    mov x1, x0
    mov x0, x21
    bl push
    bl alloc
    str w22, [x0]
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

/-- info: 51 -/
#guard_msgs in
#eval arenaP.length

/-- **The functions are the allocation pilot's, unchanged**: from `alloc:` on the two texts
are equal. -/
theorem arenaP_funs : Program.fromLabel arenaP "alloc" = Program.fromLabel allocP "alloc" := by
  decide +kernel

/-- Text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def aLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize arenaP

instance aValid : Executable.ValidLayout (aLayout arenaP) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The end address: `42` instructions of `4` bytes. -/
def endA : Int64 := 0x100000 + 168

/-- info: true -/
#guard_msgs in
#eval decide ((aLayout arenaP).addrOf arenaP.length = endA)

/-- Thread start: `x21 = &top`, arena `[x27, x28)`, payloads `x20 = v1`, `x22 = v2`. -/
def thread (base v1 v2 : UInt64) : AArch64.State where
  exe := aLayout arenaP
  endPc := endA
  st := ({ regs := { X21 := 0x1000, X27 := base, X28 := base + 0x100, X20 := v1, X22 := v2, X30 := 0x100000 + 168 } },
    0x100000)

/-- Only `top = 0` is initialised: the arenas' words are garbage (`7`). -/
def initMem : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0), (⟨0x2000, 4⟩, 7), (⟨0x2008, 8⟩, 7), (⟨0x2010, 4⟩, 7), (⟨0x2018, 8⟩, 7),
    (⟨0x3000, 4⟩, 7), (⟨0x3008, 8⟩, 7), (⟨0x3010, 4⟩, 7), (⟨0x3018, 8⟩, 7)]

/-- The explorer: per final configuration, each thread's `(x10, w11, x27)`.
Thread `0` pushes payloads `1`, `2` at `0x2000`, `0x2010`; thread `1` pushes
`3`, `4` at `0x3000`, `0x3010`. Not run in the build (it is larger than the
allocation pilot's 3.7 min run). -/
def exploreFinals (o : ExploreOpts) : List (List (Nat × Nat × Nat)) × Bool × List String :=
  let proj := fun (ts : List AArch64.State) => ts.map fun s =>
      (s.st.1.regs.X10.toBitVec.toNat, s.st.1.regs.X11.toBitVec.toNat, s.st.1.regs.X27.toBitVec.toNat)
  let r := explore Arch.armv8 (Config.init [thread 0x2000 1 2, thread 0x3000 3 4] initMem : Config isa)
    (fun c => proj (c.threads.toList.map (·.st))) o
  (r.finals, r.boundHit, r.faults)

/-- **`arenaP` is WeakCore-lowerable** (`Lower/Lowerable.lean`). -/
theorem arenaP_wcLowerable : Program.WCLowerable arenaP := by decide

/-- The LSE2 route's `hfree`. -/
theorem arenaP_lse2Free : ∀ d ∈ arenaP, d.LSE2Free := arenaP_wcLowerable.lse2Free

variable [layout : _root_.Layout]

theorem arenaP_rmwLive : (layout arenaP).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem arenaP_phase1F [Executable.ValidLayout (layout arenaP)] : Phase1TreeF (layout arenaP) :=
  phase1TreeF_of_dirs (by dirs_phase1F arenaP)

theorem arenaP_noFault : DirsNoFault (layout arenaP) := by dirs_no_fault' arenaP

end Kraken.Promising.Lower.Arena
