/-
**`wc_rodata`'s level obligations at `tpG t`** (AArch64)

The root's `hrd` (after `A64HelloMainPreTF`, row L0-tpG) asks `HelloRd.RdPreW` at
`tpG t W` (`W` only at states of thread pointer `t`). Any `RdPreW` at `W` gives it:

- `proW_mapWK`, `allocW_mapWK`, `RdPreW.mapWK`: `wc_rodata`'s obligations up to the
  allocator's return under a pointwise change of the predicate and the outside move
  (`WakeWc.blkW_mapWK`, `nodeW_mapWK` lifted).
- `rdPreW_tpG`: `RdPreW W K` gives `RdPreW (tpG t W) K`. The root's `hrd` is
  `fun v m0 σC => rdPreW_tpG (HrdS.hrd_WSHF …)`.
-/
import Spike.Lib.A64HelloHrdS
import Spike.Lib.A64WakeWcK1
import Spike.Lib.A64WakeWcMain

namespace Spike.Lib.A64.HelloPh.HrdTp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (blkW_mapWK nodeW_mapWK tpG)
open Spike.Lib.A64.Flow.HelloRd (RdPreW)
open Spike.Lib.A64.Alloc (Call AllocW)

section Map

variable {W W' : Frag isaLSE2} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}
  (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s')
include hf

/-- A prologue's obligations under a pointwise change. -/
theorem proW_mapWK {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : Flow.AS → Ctl → Prop} (h : ProW W K exe endPc R F ms pc0 Z lim L ps J) :
    ProW W' K' exe endPc R F ms pc0 Z lim L ps J :=
  ⟨blkW_mapWK hf h.w0, nodeW_mapWK hf h.w1, blkW_mapWK hf h.w2, blkW_mapWK hf h.w3⟩

/-- `scc_rt_alloc`'s obligations under a pointwise change. -/
theorem allocW_mapWK {ms : MemSide isaLSE2} {q : Call} (h : AllocW ms q W K exe endPc R F) :
    AllocW ms q W' K' exe endPc R F :=
  ⟨blkW_mapWK hf h.e, blkW_mapWK hf h.entry, blkW_mapWK hf h.n2, nodeW_mapWK hf h.cnt, nodeW_mapWK hf h.cnt1,
    blkW_mapWK hf h.cnt2, nodeW_mapWK hf h.rmw, blkW_mapWK hf h.n4, blkW_mapWK hf h.n5, blkW_mapWK hf h.slow,
    blkW_mapWK hf h.n7, blkW_mapWK hf h.full, blkW_mapWK hf h.ok, nodeW_mapWK hf h.ok1, nodeW_mapWK hf h.ok2,
    blkW_mapWK hf h.n12, nodeW_mapWK hf h.hdr, blkW_mapWK hf h.n13, nodeW_mapWK hf h.ret⟩

/-- **`wc_rodata` up to the allocator's return** under a pointwise change. -/
theorem RdPreW.mapWK {ms : MemSide isaLSE2} {J0 J1 : Flow.AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 J1) :
    RdPreW W' K' exe endPc R F ms J0 J1 :=
  ⟨proW_mapWK hf h.pro, blkW_mapWK hf h.e, fun q hok hq => allocW_mapWK hf (h.alloc q hok hq)⟩

end Map

/-- **`wc_rodata` up to the allocator's return inside `tpG t W`** from inside `W`. -/
theorem rdPreW_tpG {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {J0 J1 : Flow.AS → Ctl → Prop} {t : UInt64}
    (h : RdPreW W K exe endPc R F ms J0 J1) : RdPreW (tpG t W) K exe endPc R F ms J0 J1 :=
  RdPreW.mapWK (fun _ _ hw hk => ⟨fun _ => hw, hk⟩) h

/-- info: 'Spike.Lib.A64.HelloPh.HrdTp.rdPreW_tpG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rdPreW_tpG

end Spike.Lib.A64.HelloPh.HrdTp
