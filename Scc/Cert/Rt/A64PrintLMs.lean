import Scc.Cert.Rt.A64MorestackCall
import Spike.Lib.A64PrintL

/-!
# `wc_printL`'s call to `scc_rt_morestack` on AArch64

`hms_printL`: the given node `hms` of `Spike.Lib.A64.PrintL.seg_printL`
(the grow stub's call to `scc_rt_morestack`, from `.ms` to `.spc` at some
ghost), by `seg_ms_call`: the stub calls with `sp` at offset `-80`, the
frame record `(fp g, ra)` at `-16`, `-8`, and the return address
`.stack_grow + 56`, which is the label `.sp_check` (`hsp`).

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/A64PrintLMs.lean` (same namespace and names).
-/

namespace Scc.Cert.Rt.A64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64}

/-- The grow stub's return address: `.stack_grow` plus its 14
instructions. -/
abbrev printLRet (lab : Label → Int64) : BitVec 64 :=
  BitVec.ofInt 64 (((lab ".L21_wc_printL.stack_grow").toInt + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4).bmod
    18446744073709551616)

end Scc.Cert.Rt.A64.Morestack
