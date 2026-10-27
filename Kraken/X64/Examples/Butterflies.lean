module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser
-- The byte-level corollary unfolds `⋆` and `Mem.Block`.
import all Kraken.SeparationMem
import all Kraken.Separation

/-!
# Butterflies: an SSE loop over two arrays

The loop walks two 16-byte-aligned float arrays `v1`, `v2` of `len` floats
(`4 * len` bytes) in 16-byte chunks, replacing `(a, b)` by `(a + b, a - b)`.
Both pointers are first advanced to one past the end of their array, and a
single negative index `rdx` counts up towards zero, so the loop needs only one
`add` and a `jl`.

We prove that the loop terminates without faulting, and that on exit the two
arrays (with some new contents) are still where they were, separated from each
other and from the frame `R`.

`butterflies_spec` is proved through the control-flow rule: the table gives the
assertion at each label (at `loop`, the loop invariant), the variant is the
bytes still to process, and `Program.WP.cfg` with `cfg_cases` produces one
`kvcgen64` obligation per block, each closed by `finish`. The arrays are two
`Mem.Blocks`, owned regions whose contents are not tracked.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.Butterflies

/-- The program: the prologue moves both pointers to the end of their array
and negates the byte count into `rdx`; each iteration of the loop does one
16-byte chunk of both arrays. -/
def butterflies_float_prog : Program := parse("
start:
    shl $2, %edx
    add %rdx, %rdi
    add %rdx, %rsi
    neg %rdx
loop:
    movaps (%rdi,%rdx,1), %xmm0
    movaps (%rsi,%rdx,1), %xmm1
    movaps %xmm0, %xmm2
    subps %xmm1, %xmm2
    addps %xmm1, %xmm0
    movaps %xmm2, (%rsi,%rdx,1)
    movaps %xmm0, (%rdi,%rdx,1)
    add $16, %rdx
    jl loop
")

/- The `jl` exit reads the overflow flag, which compares signed values. -/
attribute [local grind =] BitVec.signed_eq

theorem butterflies_spec [Host] [FunDecls] (d : MachineData) (len : Nat)
    (h_len_reg : (d.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_bound : len * 4 < 2 ^ 31) (h_len_gt : len > 0)
    (h_v1_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_v2_aligned : isAligned 16 (d.regs.get64 .rsi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆
      Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R) :
    WP.wp butterflies_float_prog
      (fun _ s => s.dmem =⋆
        Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R)
      (fun _ _ => False) d := by
  refine Program.WP.cfg
    (fun b s =>
      let L := len * 4
      match b with
      | .entry | .label "start" => s = d
      | .label "loop" =>
        let j := (-s.regs.get64 .rdx).toNat
        s.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 L
          ∧ s.regs.get64 .rsi = d.regs.get64 .rsi + BitVec.ofNat 64 L
          ∧ 0 < j ∧ j ≤ L ∧ j % 16 = 0 ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
          ∧ (s.regs.get64 .rdi + s.regs.get64 .rdx - d.regs.get64 .rdi).toNat + j = L
          ∧ (s.regs.get64 .rsi + s.regs.get64 .rdx - d.regs.get64 .rsi).toNat + j = L
          ∧ s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L), (d.regs.get64 .rsi, L)] ⋆ R
      | .exit => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L), (d.regs.get64 .rsi, L)] ⋆ R
      | _ => False)
    (fun l s => match l with
      | "loop" => (-s.regs.get64 .rdx).toNat
      | _ => 2 ^ 64) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- `butterflies_spec`, read at the machine: from the program's first
directive, the run reaches the program's end with the two blocks in place.
(This was `ButterfliesBlocks.lean`, whose triple was `butterflies_spec`.) -/
theorem butterflies_blocks_terminates_and_safe [Host] [FunDecls] [he : Embeds butterflies_float_prog]
    (s₀ : MachineData) (len : Nat)
    (h_len_reg : (s₀.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_bound : len * 4 < 2 ^ 31) (h_len_gt : len > 0)
    (h_v1_aligned : isAligned 16 (s₀.regs.get64 .rdi) = true)
    (h_v2_aligned : isAligned 16 (s₀.regs.get64 .rsi) = true)
    (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆
      Mem.Blocks [(s₀.regs.get64 .rdi, len * 4), (s₀.regs.get64 .rsi, len * 4)] ⋆ R) :
    Eventually (step1 Host.exe)
      (fun u => u.data.dmem =⋆
        Mem.Blocks [(s₀.regs.get64 .rdi, len * 4), (s₀.regs.get64 .rsi, len * 4)] ⋆ R)
      ⟨s₀, he.embedding.startAddr⟩ :=
  Program.step1_of_wp
    (butterflies_spec s₀ len h_len_reg h_len_mod h_len_bound h_len_gt h_v1_aligned h_v2_aligned R h_mem)
    (fun _ _ h => h) (fun _ h => h.elim)

/-- `butterflies_spec`, read at the machine over the arrays' bytes: the two
arrays, with their contents, are the two blocks, and the blocks on exit are
two arrays with some contents. -/
theorem butterflies_float_terminates_and_safe [Host] [FunDecls] [he : Embeds butterflies_float_prog]
    (s₀ : MachineData) (v1 v2 : List UInt8) (len : Nat)
    (h_len_reg : (s₀.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_bound : len * 4 < 2 ^ 31) (h_len_gt : len > 0)
    (h_v1_len : v1.length = len * 4) (h_v2_len : v2.length = len * 4)
    (h_v1_aligned : isAligned 16 (s₀.regs.get64 .rdi) = true)
    (h_v2_aligned : isAligned 16 (s₀.regs.get64 .rsi) = true)
    (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v1.At (s₀.regs.get64 .rdi)) ⋆ Eq (v2.At (s₀.regs.get64 .rsi)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun u => ∃ (v1' v2' : List UInt8), v1'.length = len * 4 ∧ v2'.length = len * 4
        ∧ u.data.dmem =⋆ Eq (v1'.At (s₀.regs.get64 .rdi)) ⋆ Eq (v2'.At (s₀.regs.get64 .rsi)) ⋆ R)
      ⟨s₀, he.embedding.startAddr⟩ := by
  have hw : len * 4 ≤ 2 ^ 64 := by omega
  obtain ⟨m12, mR, hu, hi, ⟨m1, m2, hu', hi', rfl, rfl⟩, hR⟩ := h_mem
  refine eventually_weaken _ _ _ _ ?_ (butterflies_blocks_terminates_and_safe s₀ len h_len_reg
    h_len_mod h_len_bound h_len_gt h_v1_aligned h_v2_aligned R
    ⟨_, mR, hu, hi, ⟨_, _, hu', hi', ⟨hw, v1, h_v1_len, rfl⟩, ⟨hw, v2, h_v2_len, rfl⟩⟩, hR⟩)
  rintro u ⟨m12, mR, hu, hi, ⟨m1, m2, hu', hi', ⟨-, v1', h1, rfl⟩, ⟨-, v2', h2, rfl⟩⟩, hR⟩
  exact ⟨v1', v2', h1, h2, _, mR, hu, hi, ⟨_, _, hu', hi', rfl, rfl⟩, hR⟩

end Kraken.Examples.Butterflies
