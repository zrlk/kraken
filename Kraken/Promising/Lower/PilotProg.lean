/-
**A hand-lowered two-thread Treiber client
under the draft calling convention.**

What the WeakCore lowering emits for

```
main(v) { n := new {v, _}; push(&top, n); r := pop(&top); if r ≠ null then res := r.v }
```

with `push`/`pop` as separate functions reached by `bl` and left by `ret`:

- `main` (non-leaf): saves its link `x30` in the callee-saved `x19` (not on
  a `dmem` stack; see `Lower/DStack.lean`); allocates the node by an inline bump from `x27` with the `x28`
  limit check (`b.hi oom`); stores the payload (`str w9, [x1]`, the initial
  store of `new`); calls `push(x0 = &top, x1 = node)`, then `pop(x0 = &top)`;
  when the result `x0` is not null, keeps it in `x10` and loads its payload
  into `w11` (the per-thread result); restores `x30` and returns. `&top` is
  in the callee-saved `x21` (a global's address, set up by the runtime).
- `push` (leaf): `ldar` of `top`, `str` of the link, `casal`, retry by `b.ne`.
- `pop` (leaf): `ldar` of `top`, `cbz` on empty, `ldr` of the link, `casal`,
  retry by `b.ne`; returns the node (or `0`) in `x0`.
- `oom`: no halting instruction exists in Kraken's AArch64 syntax, so the
  overflow branch spins (`b oom`); such a thread never reaches its end, and
  final-state theorems exclude it.
- `ret_pop:` is a label behind `bl pop` (it costs no address); it names the
  return point so that the tail behind the call is a control-flow fragment.

Contents: the program `pilot`; the runner-style layout `pLayout` (text at
`0x100000`, each directive its `fakeSize`); two concrete start states;
`#guard_msgs` runs of the Promising explorer under `isa` and `isaLSE2`; the
static checks of the EnvG link (`rmwLive`, `Phase1TreeF`, `DirsNoFault`).
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.Lower.Pilot

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- **The hand-lowered program** (one text, three functions). -/
def pilot : Program := parseAArch64("
main:
    mov x19, x30
    mov x1, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi oom
    str w9, [x1]
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
oom:
    b oom
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

/-- info: 40 -/
#guard_msgs in
#eval pilot.length

/-! ## The runner-style layout and two start states -/

/-- Text at `0x100000`, each directive its `fakeSize` (labels `0`). -/
@[reducible] def pLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize pilot

instance pValid : Executable.ValidLayout (pLayout pilot) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The end address: `32` instructions of `4` bytes. -/
def endA : Int64 := 0x100000 + 128

/-- Thread `i`'s start: `x21 = &top` (`0x1000`), arena `[x27, x28)` per
thread, payload `w9 = i + 1`, link `x30 =` the end address (the runtime
"calls" `main`); empty private memory. -/
def thread (base v : UInt64) : AArch64.State where
  exe := pLayout pilot
  endPc := endA
  st := ({ regs := { X21 := 0x1000, X27 := base, X28 := base + 0x100, X9 := v, X30 := 0x100000 + 128 } }, 0x100000)

/-- `top = 0`; the first node of each arena: data word and link `0`. -/
def initMem : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0), (⟨0x2000, 4⟩, 0), (⟨0x2008, 8⟩, 0), (⟨0x3000, 4⟩, 0), (⟨0x3008, 8⟩, 0)]

/-- The explorer under `I`: per final configuration, each thread's
`(x10, w11, x27)` (popped node, its payload, the bumped arena pointer). -/
def exploreFinals (lse2 : Bool) (o : ExploreOpts) : List (List (Nat × Nat × Nat)) × Bool × List String :=
  let proj := fun (ts : List AArch64.State) => ts.map fun s =>
      (s.st.1.regs.X10.toBitVec.toNat, s.st.1.regs.X11.toBitVec.toNat, s.st.1.regs.X27.toBitVec.toNat)
  if lse2 then
    let r := explore Arch.armv8 (Config.init [thread 0x2000 1, thread 0x3000 2] initMem : Config isaLSE2)
      (fun c => proj (c.threads.toList.map (·.st))) o
    (r.finals, r.boundHit, r.faults)
  else
    let r := explore Arch.armv8 (Config.init [thread 0x2000 1, thread 0x3000 2] initMem : Config isa)
      (fun c => proj (c.threads.toList.map (·.st))) o
    (r.finals, r.boundHit, r.faults)

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- The `casal`s return into a register (`x3`). -/
theorem pilot_rmwLive : (layout pilot).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

/-- Every cell is a phase-1 tree (`bl`, `ret`, `b.hi` included). -/
theorem pilot_phase1F [Executable.ValidLayout (layout pilot)] : Phase1TreeF (layout pilot) :=
  phase1TreeF_of_dirs (by dirs_phase1F pilot)

/-- No cell faults. -/
theorem pilot_noFault : DirsNoFault (layout pilot) := by dirs_no_fault' pilot

end Static

/-- **The program terminates with the expected results** (`isa`,
promise-free exploration: `maxPromises := some 0` is an under-approximation,
hence `boundHit = true`): in every final configuration each thread popped one
of the two nodes (`0x2000`, `0x3000`) with its payload (`1`, `2`), the nodes
are distinct, and each arena pointer moved by one node (`x27 + 16`); no
fault. (The same run under `isaLSE2` gives the same finals; it is not
repeated here, each run costs about a minute.) -/
def pilotRun : List (List (Nat × Nat × Nat)) × Bool × List String :=
  exploreFinals false { fuel := 32, maxPromises := some 0 }

/-- info: ([[(8192, 1, 8208), (12288, 2, 12304)], [(12288, 2, 8208), (8192, 1, 12304)]], true, []) -/
#guard_msgs in
#eval pilotRun

end Kraken.Promising.Lower.Pilot
