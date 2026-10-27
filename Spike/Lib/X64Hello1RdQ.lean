/-
**`rodata`'s allocation premise `hQ : rdQ.OK` from the memory side alone**
(x86-64): the source's half of `Call.OK` at `rdQ` (the allocation at
`rdCN`, its count `2`, no hold, the element type's accesses) holds by
computation; `rdQ_ok` leaves only the memory side's fields: the counter's
and the arena's labels (`hctr`, `hheap`), the arena's room and cells, the
units and offset of `2` lane words, and the runtime reads, maps and value
invariant at the counter and the headers.

At the consumer's `msOf` as it stands (`MemSide.ofLabels`' defaults:
`heap = ctr = cells = 0`, one unit per allocation) `hctr`, `hheap`,
`hcells` and the setups' `hu : ms.units 2 τ8 = 3` do not hold
(`Spike/Test/X64MsOfHello1Gap.lean`); `hoff`, `hroom` and `hunits` do.
-/
import Spike.Lib.X64Hello1RodataSetupG

namespace Spike.Lib.X64.Flow.Hello1

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.Hello1RodataSrc (rdCN τ8)

/-- **`rdQ.OK` from the memory side's fields.** -/
theorem rdQ_ok {ms : MemSide isa} {lab : Label → Int64}
    (hctr : (lab "scc_rt_heap_use").toBitVec = BitVec.ofNat 64 ms.ctr)
    (hheap : (lab "scc_rt_heap").toBitVec.toNat = ms.heap) (hroom : ms.heap + 2 ^ 46 ≤ 2 ^ 64)
    (hcells : ms.cells = 4194304) (hunits : ms.units 2 τ8 < 2 ^ 63) (hoff : ms.off 2 τ8 = 8)
    (hrt : ms.rt (BitVec.ofNat 64 ms.ctr).toNat) (hmp : ms.mp (ctrLoc ms) true)
    (hgrow : ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
      ms.G (ctrLoc ms) ((old.setWidth 64 + rdQ.u ms).setWidth 128))
    (hdr : ∀ o, o + ms.units 2 τ8 ≤ ms.cells →
      ms.rt (rdQ.hdrAt ms o) ∧ ms.mp ⟨BitVec.ofNat 64 (rdQ.hdrAt ms o), 8⟩ true ∧
        ms.G ⟨BitVec.ofNat 64 (rdQ.hdrAt ms o), 8⟩ (rdQ.hdr.setWidth 128)) :
    rdQ.OK ms lab where
  term := rfl
  ev := rfl
  num := by decide
  hold := rfl
  n_lt := by decide
  ctr := hctr
  heap := hheap
  room := hroom
  cells := hcells
  units := hunits
  off := by show ms.off 2 τ8 = _; rw [hoff]; decide
  accs := ⟨_, rfl⟩
  rt := hrt
  mp := hmp
  grow := hgrow
  hdr := hdr

end Spike.Lib.X64.Flow.Hello1
