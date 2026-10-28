module

public import Kraken.StateCfg
public import Kraken.X64.WP.Image
import Kraken.X64.Parser

/-!
# A lookup in a constant byte table

```
tbl_lookup:                    ; returns tbl[rdi], the number of set bits of rdi < 16
    lea     rcx, [rip + tbl]
    movzx   eax, byte ptr [rcx + rdi]
    ret
    .align 16
tbl:
    .byte 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4
```

The table sits behind the `ret`, as a compiler places a constant pool in the
text section. The precondition only says that the program's image is loaded
(`Host.Image`); it does not list the table or its bytes. The value of the
lookup comes from the `.byte` line: `Host.Image.contains` gives the table's
bytes at `tbl` from the image, and `Mem.Contains.loadInt` reads the byte at the
symbolic index.

`tbl_lookup_spec`: entered with a return address `ra` on the stack and
`rdi < 16`, `tbl_lookup` returns to `ra` with the table entry for `rdi` in
`rax`, the stack popped, and memory unchanged.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.ByteTable

def byte_table_body : Program := parse("
tbl_lookup:
    lea tbl(%rip),%rcx
    movzbl (%rcx,%rdi),%eax
    ret
    .align 16
tbl:
    .byte 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4
")

/-- The bytes of the table, as written in the program. -/
def tbl_bytes : List UInt8 := [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4]

/-- A byte read at `a + x`, inside the cell at `a`. The address is spelled as the
`sib1` rule leaves it. -/
theorem loadInt_tbl {m : DataMem} {a x : BitVec 64} (h : Mem.Contains m a tbl_bytes)
    (hx : x.toNat < 16) : m.loadInt (a + x + 0#64) 1 = some ((tbl_bytes[x.toNat]!).toNat : Int) := by
  have hx' : (a + x + 0#64 - a).toNat = x.toNat := by
    rw [BitVec.add_zero, BitVec.add_comm, BitVec.add_sub_cancel]
  have := h.loadInt (addr := a + x + 0#64) (by rw [hx']; exact hx)
  rwa [hx'] at this

/-- The zero-extended byte is the byte's value. -/
theorem zeroExtend_ofInt_byte (b : UInt8) :
    ((BitVec.ofInt 8 (b.toNat : Int)).zeroExtend 32).zeroExtend 64 = BitVec.ofNat 64 b.toNat := by
  have hb := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat]
  omega

attribute [local grind =] zeroExtend_ofInt_byte

theorem tbl_lookup_spec [Host] [FunDecls] [he : Embeds byte_table_body] (s : MachineData) (ra : Int64)
    (R : DataMem → Prop) :
    ⦃ fun t => t = s.pushRa ra ∧ (s.regs.get64 .rdi).toNat < 16 ∧ t.dmem =⋆ Host.Image ⋆ R ⦄
      byte_table_body
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rax = BitVec.ofNat 64 (tbl_bytes[(s.regs.get64 .rdi).toNat]!).toNat
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = (s.pushRa ra).dmem ⦄ := by
  refine ⟨fun t₀ ⟨h₀, hx, himg⟩ => ?_⟩
  subst h₀
  -- the table's bytes, from the image
  have hc : Mem.Contains (s.pushRa ra).dmem (label "tbl").toBitVec tbl_bytes :=
    Host.Image.contains himg he.embedding.isInfixAt (i := 5) rfl rfl (by decide)
  have hload := loadInt_tbl hc hx
  refine Program.WP.cfg (fun
      | .entry, t | .label "tbl_lookup", t => t = s.pushRa ra
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end Kraken.Examples.ByteTable
