/-
**hello.w's region depths on x86-64** (the depth constants of `Spike/Lib/A64HelloStartH0G.lean`, split out so
the root's pinned ghost can name them before the start's glue exists): `helloD`, the depth of `wc_main`'s region
below `wc_rodata`'s call (`HelloM.wcR R helloD = R.callee (-80) (-helloD) 8`), and `helloLsw`, the depth of the
new stack's region (the return address `call scc_rt_main` pushes and `scc_rt_main`'s frame `80` above `helloD`).

- `helloD`, `helloLsw`: the depths.
- `helloD_bounds`: AArch64's bounds on them.
- `helloD_fit`: `wc_main`'s region fits in `scc_rt_main`'s (`MainGlue.RS helloLsw v`).
- `helloD_ti`: the box's frame (`wcR … helloD` re-based at the saved `%rbp`, lower bound `-helloD + 8`) meets
  the bound the second `scc_rt_thread_init` call's nodes need (`R.lo ≤ -384`).

Unlike AArch64, the bounds are read against x86-64's frames: `wc_main`'s frame is 128 with the allocator's 160
below its pushed return address (`WcPreWH` needs `R.lo ≤ -304`, as AArch64's 144 + 160), and the second take's
nodes need `R.lo ≤ -384`; AArch64's `helloD = 400` meets both and is kept. `scc_rt_main` is entered by a `call`, so
its region is `MainGlue.RS Lsw v = (swR v (-Lsw) 0).callee (-8) (8 - Lsw) 8` (AArch64: `swR v (-Lsw) 0` itself),
and `wc_main`'s region `wcR (RS Lsw v) helloD` reaches `-8 - 80 - helloD` below the switch base: `helloLsw` is
`488` (AArch64 `480`).
-/
import Spike.Lib.X64HelloMain
import Spike.Lib.X64WakeMainGlue

namespace Spike.Lib.X64.HelloPh.StartH0G

/-- **hello's `wc_main` region depth** below `wc_rodata`'s call (`wc_main`'s frame, the allocator's, and the heap
abort's dispatcher and stub). -/
abbrev helloD : Int := 400

/-- **hello's new-stack region depth** (`call scc_rt_main`'s return address `8` and its frame `80` above
`helloD`). -/
abbrev helloLsw : Int := 488

/-- **The depths' bounds** (AArch64's statement). -/
theorem helloD_bounds : 304 ≤ helloD ∧ helloD % 16 = 0 ∧ 80 + helloD ≤ helloLsw ∧ helloLsw % 8 = 0 ∧
    helloLsw ≤ 12288 ∧ 288 ≤ helloLsw ∧ 80 + 48 + 208 ≤ helloLsw ∧ helloLsw - 80 - 208 ≥ 48 ∧
    -helloD ≤ -304 - 48 := by
  decide

/-- **The box's frame reaches the second take's nodes' bound** (`R.lo ≤ -384` at `(wcR … helloD).fp (-8)`). -/
theorem helloD_ti : -helloD + 8 ≤ -384 := by decide

/-- **`wc_main`'s region fits in `scc_rt_main`'s**: `RS helloLsw v`'s lower bound reaches `wcR`'s callee
bounds (`8 + 80 + helloD ≤ helloLsw`). -/
theorem helloD_fit : 8 + 80 + helloD ≤ helloLsw := by decide

/-- `wc_main`'s region at a concrete base is a region with its lower bound `-helloD` (non-vacuity of the
depths). -/
example :
    (Spike.Lib.X64.Flow.HelloM.wcR (Spike.Lib.X64.WakePh.MainGlue.RS helloLsw 0x10000#64) helloD).lo = -helloD := by
  simp [Spike.Lib.Region.callee]

end Spike.Lib.X64.HelloPh.StartH0G

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.StartH0G.helloD_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0G.helloD_bounds
