import Kraken.EnvVCGen
import Kraken.X64.Parser

/-!
# `vcgen` over the environment wp: VEX moves on shared locations

`vexShared` stores a 32-byte register with `vmovdqu` (four 8-byte pieces in
address order) and loads an aligned 16-byte value with `vmovdqa` (one
atomic access), both on shared locations, in `SharedEnv.lastWrite`:
`vcgen` with the two rules passed (`vmovdqa_load_shared_spec`,
`vmovdqu_store_shared_spec`, not registered); `SharedEnv.AvxLoad`/`AvxStore`
reduce at the width literals (`AvxWidth.W128_beq_W128`, `AvxLoad_true`,
`AvxStore_false`), and `vcgen` does not enter the pieces' continuations.
`vcgen_env` does: it takes the access and each piece by its introduction
rule (`SharedEnv.AvxStore.intro_pieces`, `StorePieces.intro_cons`, …) and
calls `vcgen` again behind them, so one call covers the program and one
`simp_all` the side conditions.
-/

open Std.WP
open Kraken
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

section

open Kraken.X64.Parser

variable [layout : _root_.Layout]

/-- A 32-byte store in pieces and an atomic 16-byte load. -/
def vexShared : Program := parse("
  vmovdqu %ymm1, (%rsi)
  vmovdqa (%rdi), %xmm0
")

local instance vexShared.env : CodeEnv := ⟨layout vexShared⟩

theorem vexShared_correctEnv (d : MachineData)
    (h_al : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_src : Mem.loadInt d.dmem (d.regs.get64 .rdi) 16 = none)
    (h_dst : Mem.loadInt d.dmem (d.regs.get64 .rsi) 32 = none) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.get64 .rdi, 16), (d.regs.get64 .rsi, 8),
        (d.regs.get64 .rsi + 8, 8), (d.regs.get64 .rsi + 16, 8), (d.regs.get64 .rsi + 24, 8)])
      (fun s _ => s = d)
      vexShared
      (fun s g => ∃ v : BitVec 128, s.zmms = d.zmms.set (.xmm .mm0) v ∧
        (g (d.regs.get64 .rsi + 24)).setWidth 64 = (d.zmms.get (.ymm .mm1)).extractLsb' 192 64)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold vexShared
  vcgen_env [vmovdqu_store_shared_spec, vmovdqa_load_shared_spec]
  all_goals subst_vars
  all_goals simp_all [SharedEnv.lastWrite, SharedEnv.upd, BitVec.add_assoc]
  exact ⟨_, rfl⟩

/-- A 32-byte load in pieces and an aligned 32-byte store (not atomic at
this width: pieces too). -/
def vexPieces : Program := parse("
  vmovdqu (%rdi), %ymm0
  vmovdqa %ymm0, (%rsi)
")

local instance vexPieces.env : CodeEnv := ⟨layout vexPieces⟩

/-- `vcgen_env` through `LoadPieces` (four loads) and an `AvxStore` at
`W256` (`intro_pieces`, four stores): `ymm0` is loaded, and its top piece is
the last one stored. -/
theorem vexPieces_correctEnv (d : MachineData)
    (h_al : isAligned 32 (d.regs.get64 .rsi) = true)
    (h_src : Mem.loadInt d.dmem (d.regs.get64 .rdi) 32 = none)
    (h_dst : Mem.loadInt d.dmem (d.regs.get64 .rsi) 32 = none) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.get64 .rdi, 8), (d.regs.get64 .rdi + 8, 8),
        (d.regs.get64 .rdi + 16, 8), (d.regs.get64 .rdi + 24, 8), (d.regs.get64 .rsi, 8),
        (d.regs.get64 .rsi + 8, 8), (d.regs.get64 .rsi + 16, 8), (d.regs.get64 .rsi + 24, 8)])
      (fun s _ => s = d)
      vexPieces
      (fun s g => (∃ v : BitVec 256, s.zmms = d.zmms.set (.ymm .mm0) v) ∧
        (g (d.regs.get64 .rsi + 24)).setWidth 64 = (s.zmms.get (.ymm .mm0)).extractLsb' 192 64)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold vexPieces
  vcgen_env [vmovdqu_load_shared_spec, vmovdqa_store_shared_spec]
  all_goals subst_vars
  all_goals simp_all [SharedEnv.lastWrite, BitVec.add_assoc]
  exact ⟨_, rfl⟩

end
