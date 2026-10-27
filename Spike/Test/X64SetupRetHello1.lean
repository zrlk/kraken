/-
**`SetupPostS` on `hello1.w`** (x86-64): `wc_rodata`'s return as its last
block leaves it (`rpB4`: the buffer's base in `%rax`, `0` in `%rdx`, `2` in
`%rcx`, `13` in `%rsi`) with the source at `rodata`'s `ret sl` is the named
post at `hello1Pl`.
-/
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.Rt.X64SetupRet

namespace Spike.Test.X64SetupRetHello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.SetupRet
open Spike.Lib.X64.Rt (rdX64)

/-- **`wc_rodata`'s return registers and `ret sl` are `SetupPostS` at
`hello1Pl`.** -/
theorem rdRet_setupPostS {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {ini : Nat}
    {wo0 wo1 : TermRun.Word} {r : Reg64s} (hl : lbl l = some r.rax.toNat) (hdx : r.rdx.toBitVec = 0#64)
    (hcx : r.rcx.toBitVec = 2#64) (hsi : r.rsi.toBitVec = 13#64) :
    SetupPostS lbl rdX64 hello1Pl (Spike.Lib.Hello1RodataSrc.rdRet l ini wo0 wo1) r := by
  refine ⟨rfl, _, _, _, rfl, rfl, ⟨rfl, hl, ?_⟩, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩, trivial⟩
  · show r.rdx.toBitVec.toNat = 8 * 0
    rw [hdx]; rfl
  · show r.rcx.toBitVec.toNat = 2
    rw [hcx]; rfl
  · show r.rsi.toBitVec.toNat = 13
    rw [hsi]; rfl

end Spike.Test.X64SetupRetHello1
