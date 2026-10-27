module

public import Kraken.StateCfg
import Kraken.X64.Parser

/-!
# A jump through an address the program stores itself

```
store_jump:                          ; returns 42
    lea     rax, [rip + .Ltarget]
    mov     qword ptr [rsp - 8], rax ; red-zone slot
    jmp     qword ptr [rsp - 8]
.Lbad:
    xor     eax, eax
    ret
.Ltarget:
    mov     eax, 42
    ret
```

`store_jump_spec`: entered with a return address `ra` on the stack (the entry
state is `s.pushRa ra` for the caller's state `s`) and the slot below it
writable, `store_jump` returns to `ra` with 42 in `rax` and the stack popped.
The memory is as on entry except the slot, which holds `.Ltarget`'s address.

## Findings

The label address survives a round trip through memory: from the register as
a `BitVec`, stored as an `Int` (`toInt`) in 8 bytes, loaded back as an `Int`,
and decoded to the jump target as an `Int64`. The lemmas that read back a
pushed return address (`Mem.loadInt_storeInt_64`,
`Int64.ofBitVec_ofBytes_toBytes`, in `Kraken.StateCfg`) cover this.

The store must not disturb the return address that `ret` reads at `[rsp]`,
8 bytes above the slot: `Mem.loadInt_storeInt_of_above` (in `Mem.lean`) says
that a load that starts at least `n` bytes above an `n`-byte store, without
wrapping around, reads what was there before. `loadInt_storeInt_below` states
it at the slot's address as `kvcgen64` leaves it, for `grind`.

The cfg rule reads a jump to an address as a jump to every label at that
address, so the proof first shows that `.Ltarget` shares its address with no
other label of the body (`hne0`, `hne1`, from the placement `Embeds`).
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.StoreJump

def store_jump_body : Program := parse("
store_jump:
  leaq .Ltarget(%rip), %rax
  movq %rax, -8(%rsp)
  jmp *-8(%rsp)
.Lbad:
  xorl %eax, %eax
  ret
.Ltarget:
  movl $42, %eax
  ret
")

/-- The slot below the return address. -/
abbrev slot (t : MachineData) : BitVec 64 := t.regs.get64 .rsp - 8

/-- The memory after the store: the slot holds `.Ltarget`'s address. -/
abbrev stored [Host] (t : MachineData) : DataMem :=
  Mem.storeInt t.dmem (slot t) 8 (label ".Ltarget").toBitVec.toInt

/-- The jump reads back what the store wrote. -/
theorem get!_loadInt_storeInt (m : DataMem) (a : BitVec 64) (v : Int) :
    ((m.storeInt a 8 v).loadInt a 8).get! = Int.ofBytes (Int.toBytes 8 v) := by
  rw [Mem.loadInt_storeInt_64, Option.get!_some]

/-- A store to the slot below `r` leaves the return address at `r` alone. The
displacement is spelled as `kvcgen64` leaves it. -/
theorem loadInt_storeInt_below (m : DataMem) (r : BitVec 64) (v : Int) :
    (Mem.storeInt m (r + 18446744073709551608#64) 8 v).loadInt r 8 = m.loadInt r 8 := by
  have h : (r - (r + 18446744073709551608#64)).toNat = 8 := by
    rw [show r - (r + 18446744073709551608#64) = 8#64 by grind]; rfl
  exact Mem.loadInt_storeInt_of_above m _ r 8 8 v (by omega) (by omega)

attribute [local grind =] get!_loadInt_storeInt loadInt_storeInt_below

theorem store_jump_spec [Host] [FunDecls] [he : Embeds store_jump_body] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ (Mem.loadInt t.dmem (slot t) 8).isSome = true ⦄
      store_jump_body
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = stored (s.pushRa ra)
      ∧ t.regs.get64 .rax = 42 ⦄ := by
  -- `.Ltarget` is not at the address of another label of the body
  have hk := he.embedding.isInfixAt
  generalize he.embedding.start = k at hk
  have hne0 : label "store_jump" ≠ label ".Ltarget" := by
    rw [Host.label_eq hk (i := 0) rfl, Host.label_eq hk (i := 7) rfl]
    exact Host.addrOf_ne (m := k + 1) (List.isInfixAt_iff_getElem?.mp hk 1 (by decide))
      (by rintro ⟨⟩) (by omega) (by omega)
  have hne1 : label ".Lbad" ≠ label ".Ltarget" := by
    rw [Host.label_eq hk (i := 4) rfl, Host.label_eq hk (i := 7) rfl]
    exact Host.addrOf_ne (m := k + 5) (List.isInfixAt_iff_getElem?.mp hk 5 (by decide))
      (by rintro ⟨⟩) (by omega) (by omega)
  refine ⟨fun t₀ ⟨h₀, hslot⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "store_jump", t => t = s.pushRa ra
      | .label ".Ltarget", t => t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp
          ∧ t.dmem = stored (s.pushRa ra) ∧ t.retAddr = some ra
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end Kraken.Examples.StoreJump
