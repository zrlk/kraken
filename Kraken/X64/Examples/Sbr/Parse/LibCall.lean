import Kraken.X64.Examples.Sbr.Spec

/-!
# Callee contracts for the parser proofs

`memcpy(dst, src, n)` with its effect: the destination holds the source bytes afterwards.
(`MemcpySpec` of `Spec.lean` only keeps the two regions owned, which is all `ff_aac_sbr_apply`
needs; a parser routine that builds a table by copying needs the values.) Assumed, like the
other library contracts: it is what the C standard specifies for non-overlapping regions.
`memset(dst, c, n)` likewise: `dst[n]` holds `n` copies of `(unsigned char)c` afterwards
(`MemsetSpec` of `Spec.lean` only keeps the region owned).
-/

open Kraken Kraken.SysV Mem
open Kraken.Examples.Sbr

namespace Kraken.Examples.Sbr.Parse

variable [CodeEnv]

/-- `memcpy(dst, src, n)`'s logical variables: the caller's memory `R` and the source bytes. -/
structure McA where
  R : Mem 64 → Prop
  src : List UInt8

/-- `src[n]` (`n` the length of `src`) read, `dst[n]` written, the two disjoint (separate
cells) and disjoint from the caller's memory. -/
abbrev McPre (need : Nat) (x : McA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need ((x.src =@ arg1 t ⋆ (arg2 t).toNat ?@ arg0 t) ⋆ x.R) ra t
    ∧ x.src.length = (arg2 t).toNat

/-- Afterwards `dst[n]` holds the source bytes; the source and the caller's memory are kept. -/
abbrev McPost (need : Nat) (x : McA) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost need ((x.src =@ arg1 t ⋆ x.src =@ arg0 t) ⋆ x.R) ra t s

/-- Assumed: `memcpy` copies, with `need` bytes of stack. -/
abbrev MemcpyValSpec (need : Nat) : Prop :=
  cenv.ProcSpec (entry "memcpy") (McPre need) (McPost need)

/-- `memset(dst, c, n)`'s logical variables: the caller's memory `R`. -/
structure MsA where
  R : Mem 64 → Prop

/-- `dst[n]` owned (any contents), disjoint from the caller's memory. -/
abbrev MsPre (need : Nat) (x : MsA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need ((arg2 t).toNat ?@ arg0 t ⋆ x.R) ra t

/-- Afterwards `dst[n]` holds `n` copies of `(unsigned char)c`, `rax = dst`; the caller's
memory is kept. -/
abbrev MsPost (need : Nat) (x : MsA) (ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rax = arg0 t
  ∧ CallPost need
      (List.replicate (arg2 t).toNat (UInt8.ofBitVec ((arg1 t).setWidth 8)) =@ arg0 t ⋆ x.R) ra t s

/-- Assumed: `memset` fills (the C standard's `memset`), with `need` bytes of stack. -/
abbrev MemsetValSpec (need : Nat) : Prop :=
  cenv.ProcSpec (entry "memset") (MsPre need) (MsPost need)

end Kraken.Examples.Sbr.Parse
