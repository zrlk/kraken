/-
**The allocation-capable consumer's arena premises on `hello1.w`'s AArch64
layout** (`correctKA`'s `hok`, `hstat`, `hsub`, `hal`, `hz0`, `hc0` are
satisfiable): the arena `Arena.ofWords 0x1000000 (2^22) 0x600000 (fun _ => 0)`
(the link's heap region `scc_rt_heap`, `2^22` cells of 16 bytes, the counter
word `scc_rt_heap_use` in `.data`, no trace words in a header, the runtime's
`scc_rt_alloc` with `h = 257`) meets `Arena.OK`, places `hello1`'s buffer of
two bytes at offset 8 in 3 units, lies in the layout's
heap region, 16-aligned; the static link places no label; and no initial
word of the canonical load (`Rt.A64.initOf`) is in the arena or at the
counter (`ArenaInit.arenaInitOk`), so both start zero. Pins the premises'
non-vacuity on the real layout.
-/
import Spike.Lib.ArenaInit
import Spike.Lib.A64ConsumerA
import Spike.Lib.A64Hello1Code
import Scc.Cert.Rt.RtInitA64

namespace Spike.Test.A64ArenaHello1

open Kraken.Promising
open Scc.Sem (Range wordLoc)
open Spike.Lib (Arena)
open SccCode (hello1Λ hello1Prog hello1Secs)

/-- `hello1.w`'s arena: the heap region, its cells, the counter word, no
trace words in a header. -/
def ar : Arena := Arena.ofWords 0x1000000 (2 ^ 22) 0x600000 (fun _ => 0)

/-- The counter is `scc_rt_heap_use`'s address in the link. -/
theorem ctr_eq : Scc.Cert.Rt.A64.rtA hello1Λ hello1Prog hello1Secs "scc_rt_heap_use" = BitVec.ofNat 64 ar.ctr := by
  decide +kernel

/-- The link's heap region is the arena's range. -/
theorem heap_eq : hello1Λ.heap = ⟨ar.heap, 16 * ar.cells⟩ := by decide +kernel

/-- The counter word is in `.data`. -/
theorem ctr_data : hello1Λ.data.contains ar.ctr := by decide +kernel

/-- `hok`. -/
theorem ar_ok : ar.OK := Arena.ofWords_ok (by decide) (by decide) (by decide) fun _ _ _ => Nat.zero_le _

/-- `hello1`'s buffer of two bytes: its base 8 bytes into the object (past
the header word). -/
theorem off_bytes2 : ar.off 2 (.lanes false .w8) = 8 := by decide

/-- `hello1`'s buffer of two bytes: 3 units (two words and the header). -/
theorem units_bytes2 : ar.units 2 (.lanes false .w8) = 3 := by decide

/-- `hstat`. -/
theorem stat : hello1Λ.static = fun _ => none := rfl

/-- `hsub`. -/
theorem sub : (Range.mk ar.heap (16 * ar.cells)).Sub hello1Λ.heap := by
  rw [heap_eq]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- `hal`. -/
theorem al : ar.heap % 16 = 0 := by decide

/-- The arena below `2^64` (`initVal_arena`'s premise). -/
theorem ar_lt : ar.heap + 16 * ar.cells ≤ 2 ^ 64 := by decide

/-- No initial word of the canonical load in the arena or at the counter. -/
theorem init_ok :
    Spike.Lib.ArenaInit.arenaInitOk (Scc.Cert.Rt.A64.initOf hello1Λ hello1Prog hello1Secs) ar.heap ar.cells ar.ctr =
      true := by
  decide +kernel

/-- `hz0` for a memory with the canonical load's initial words. -/
theorem z0 {m : Memory} (hm : m.init = Scc.Cert.Rt.A64.initOf hello1Λ hello1Prog hello1Secs) {a : Nat}
    (ha : (Spike.Lib.AllocRow.freeR ar.heap ar.cells 0).contains a) : m.initVal (wordLoc a) = 0 :=
  Spike.Lib.ArenaInit.initVal_arena (by rw [hm]; exact init_ok) ar_lt ha

/-- `hc0` for a memory with the canonical load's initial words. -/
theorem c0 {m : Memory} (hm : m.init = Scc.Cert.Rt.A64.initOf hello1Λ hello1Prog hello1Secs) :
    m.initVal (wordLoc ar.ctr) = 0 :=
  Spike.Lib.ArenaInit.initVal_ctr (by rw [hm]; exact init_ok)

end Spike.Test.A64ArenaHello1
