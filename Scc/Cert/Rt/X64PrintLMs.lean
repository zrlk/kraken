import Scc.Cert.Rt.X64MorestackCall
import Spike.Lib.X64PrintL

/-!
# `wc_printL`'s call to `scc_rt_morestack` on x64

`hms_printL`: the given node `hms` of `Spike.Lib.X64.PrintL.seg_printL`
(the grow stub's call to `scc_rt_morestack`, from `.ms` to `.x18` at some
ghost), by `seg_ms_call`: the stub calls with the return address at offset
`-56`, the frame record `(rb g, ra)` at `0`, `8`, and the return address
`.stk + 18`, which is the label `.x18` (`hx18`).

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/X64PrintLMs.lean` (same namespace and names).
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64}

/-- The grow stub's return address: `.stk` plus its three instructions. -/
abbrev printLRet (lab : Label → Int64) : BitVec 64 := (lab ".Lwc_printL.stk" + 18).toBitVec

end Scc.Cert.Rt.X64.Morestack
