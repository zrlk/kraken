/-
**`wc_rodata`'s level obligations under a pointwise change** (x86-64; the twin of `Spike/Lib/A64HelloHrdTp.lean`'s
live part): `wc_rodata`'s obligations up to the allocator's return under a pointwise change of the predicate and
the outside move (`WakeWc.blkW_mapWK`, `nodeW_mapWK` lifted), as the root's `hrd` at `tpG t W` uses them.

- `proW_mapWK`, `allocW_mapWK`, `RdPreW.mapWK`: the prologue's, `scc_rt_alloc`'s, and `wc_rodata`'s up to the
  allocator's return.

## Differences from the AArch64 version

- The prologue is x86-64's stack-checked `XProW` (five nodes: `xHead`, the `lea`, the `%fs` load, the compare,
  the frame stores; AArch64 `ProW`, four), and `scc_rt_alloc`'s `AllocW` has x86-64's 31 nodes (AArch64 19).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `rdPreW_tpG`.
-/
import Spike.Lib.X64WakeWcK1
import Spike.Lib.X64HelloRodata

namespace Spike.Lib.X64.HelloPh.HrdTp

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (blkW_mapWK nodeW_mapWK)
open Spike.Lib.X64.Flow.HelloRd (RdPreW)
open Spike.Lib.X64.Alloc (Call AllocW)

section Map

variable {W W' : Frag isa} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}
  (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s')
include hf

/-- A stack-checked prologue's obligations under a pointwise change. -/
theorem proW_mapWK {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}
    (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J) :
    XProW W' K' exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨blkW_mapWK hf h.w0, blkW_mapWK hf h.w1, nodeW_mapWK hf h.w2, blkW_mapWK hf h.w3, blkW_mapWK hf h.w4⟩

/-- `scc_rt_alloc`'s obligations under a pointwise change. -/
theorem allocW_mapWK {ms : MemSide isa} {q : Call} (h : AllocW ms q W K exe endPc R F) :
    AllocW ms q W' K' exe endPc R F :=
  ⟨blkW_mapWK hf h.e, blkW_mapWK hf h.entry, blkW_mapWK hf h.j1, nodeW_mapWK hf h.cnt, blkW_mapWK hf h.c1,
    nodeW_mapWK hf h.rmw, blkW_mapWK hf h.c2, blkW_mapWK hf h.j2, blkW_mapWK hf h.slow, blkW_mapWK hf h.j3,
    blkW_mapWK hf h.full, blkW_mapWK hf h.ok, nodeW_mapWK hf h.f1, blkW_mapWK hf h.o1, nodeW_mapWK hf h.f2,
    blkW_mapWK hf h.o2, nodeW_mapWK hf h.s2, blkW_mapWK hf h.o3, nodeW_mapWK hf h.f3, blkW_mapWK hf h.o4,
    nodeW_mapWK hf h.f4, blkW_mapWK hf h.o5, nodeW_mapWK hf h.f5, blkW_mapWK hf h.o6, nodeW_mapWK hf h.f6,
    blkW_mapWK hf h.o7, nodeW_mapWK hf h.f7, blkW_mapWK hf h.o8, nodeW_mapWK hf h.hdr, blkW_mapWK hf h.o9,
    nodeW_mapWK hf h.ret⟩

/-- **`wc_rodata` up to the allocator's return** under a pointwise change. -/
theorem RdPreW.mapWK {ms : MemSide isa} {J0 J1 : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 J1) :
    RdPreW W' K' exe endPc R F ms J0 J1 :=
  ⟨proW_mapWK hf h.pro, blkW_mapWK hf h.e, fun q hok hq => allocW_mapWK hf (h.alloc q hok hq)⟩

end Map

end Spike.Lib.X64.HelloPh.HrdTp

/-- info: 'Spike.Lib.X64.HelloPh.HrdTp.RdPreW.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdTp.RdPreW.mapWK
