module

public import Kraken.X64.WP.Static
import Kraken.X64.Parser

/-!
# A call under the static-frame convention

```
outer:                         ; rax := tbl[tbl[rdi]]
    call    inner
    lea     rcx, [rip + tbl]
    movzx   eax, byte ptr [rcx + rax]

inner:                         ; rax := tbl[rdi]
    lea     rcx, [rip + tbl]
    movzx   eax, byte ptr [rcx + rdi]
    ret
    .align 16
tbl:
    .byte 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4
```

Both procedures read the table. `inner`'s contract (`inner_spec`) names no
constant: it is granted the image (`StaticPre`) and gives it back
(`StaticPost`), and its result is the table entry, which its proof reads from
the image. `outer` calls `inner` and then reads the table again: it has the
image back from `inner`'s postcondition, so the second read needs nothing
beyond the convention either.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP
open Program.WP (StaticPre StaticPost)

set_option experimental.vcgen true

namespace Kraken.Examples.StaticCall

def inner_body : Program := parse("
inner:
    lea tbl(%rip),%rcx
    movzbl (%rcx,%rdi),%eax
    ret
    .align 16
tbl:
    .byte 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4
")

def outer_body : Program := parse("
outer:
    call inner
    lea tbl(%rip),%rcx
    movzbl (%rcx,%rax),%eax
")

/-- The bytes of the table, as written in the program. -/
def tbl_bytes : List UInt8 := [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4]

/-- What `inner` returns for `x`. -/
abbrev tbl (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (tbl_bytes[x.toNat]!).toNat

theorem tbl_lt (x : BitVec 64) : (tbl x).toNat < 16 := by
  have h : ∀ i : Nat, (tbl_bytes[i]! : UInt8).toNat < 16 := by
    intro i
    rcases Nat.lt_or_ge i 16 with hi | hi
    · have : ∀ j : Fin 16, (tbl_bytes[j.val]! : UInt8).toNat < 16 := by decide
      exact this ⟨i, hi⟩
    · rw [getElem!_neg tbl_bytes i (by simp [tbl_bytes]; omega)]; decide
  simp only [tbl, BitVec.toNat_ofNat]
  have := h x.toNat
  omega

/-- The table, from the image, at any placement of `inner`. -/
theorem tbl_contains [Host] [he : Embeds inner_body] {m : DataMem} {F : DataMem → Prop}
    (h : m =⋆ Host.Image ⋆ F) : Mem.Contains m (label "tbl").toBitVec tbl_bytes :=
  Host.Image.contains h he.embedding.isInfixAt (i := 5) rfl rfl (by decide)

/-- A byte read in the table at index `x < 16`, the address spelled as the `sib1` rule
leaves it. -/
theorem loadInt_tbl [Host] [Embeds inner_body] {m : DataMem} {F : DataMem → Prop}
    (h : m =⋆ Host.Image ⋆ F) {x : BitVec 64} (hx : x.toNat < 16) :
    m.loadInt ((label "tbl").toBitVec + x + 0#64) 1 = some ((tbl_bytes[x.toNat]!).toNat : Int) := by
  have hx' : ((label "tbl").toBitVec + x + 0#64 - (label "tbl").toBitVec).toNat = x.toNat := by
    rw [BitVec.add_zero, BitVec.add_comm, BitVec.add_sub_cancel]
  have := (tbl_contains h).loadInt (addr := (label "tbl").toBitVec + x + 0#64) (by rw [hx']; exact hx)
  rwa [hx'] at this

/-- The zero-extended byte is the byte's value. -/
theorem zeroExtend_ofInt_byte (b : UInt8) :
    ((BitVec.ofInt 8 (b.toNat : Int)).zeroExtend 32).zeroExtend 64 = BitVec.ofNat 64 b.toNat := by
  have hb := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat]
  omega

/-- The return slot of a call made in state `s`. -/
abbrev slot (s : MachineData) : BitVec 64 := s.regs.get64 .rsp - 8#64

/-- The call's return slot can be written: it is a block of the frame. -/
theorem slot_isSome [Host] {m : DataMem} {a : BitVec 64} {R : DataMem → Prop}
    (h : m =⋆ Host.Image ⋆ (Mem.Blocks [(a, 8)] ⋆ R)) : (m.loadInt a 8).isSome = true := by
  rw [Std.ExtHashMap.sep_comm_l] at h
  exact Mem.Blocks.loadInt_isSome h (Mem.Blocks.Inside.base (Nat.le_refl 8))

/-- `inner` clobbers `rax`, `rcx` and its return slot. -/
abbrev innerMod (s : MachineData) : Modifies := ⟨[.rax, .rcx], [(slot s, 8)]⟩

attribute [local grind =] zeroExtend_ofInt_byte StaticPost

theorem inner_spec [Host] [FunDecls] [he : Embeds inner_body] (R : DataMem → Prop)
    (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra
        ∧ ((s.regs.get64 .rdi).toNat < 16 ∧ StaticPre (Mem.Blocks [(slot s, 8)] ⋆ R) s) ⦄
      inner_body
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ (t.regs.get64 .rax = tbl (s.regs.get64 .rdi) ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ StaticPost (Mem.Blocks [(slot s, 8)] ⋆ R) t)
      ∧ (innerMod s).Agree s t ⦄ := by
  refine ⟨fun t₀ ⟨h₀, hx, himg⟩ => ?_⟩
  subst h₀
  -- the image survives the push; the table read comes from it
  have hpush : (s.pushRa ra).dmem =⋆ Host.Image ⋆ (Mem.Blocks [(slot s, 8)] ⋆ R) := himg.pushRa ra
  have hload := loadInt_tbl hpush hx
  refine Program.WP.cfg (fun
      | .entry, t | .label "inner", t => t = s.pushRa ra
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- Table entries are small enough to index the table again. -/
theorem tbl_entry_lt (i : Nat) : (BitVec.ofNat 64 (tbl_bytes[i]! : UInt8).toNat).toNat < 16 := by
  have := tbl_lt (BitVec.ofNat 64 i)
  rcases Nat.lt_or_ge i 16 with hi | hi
  · simpa [tbl, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)] using this
  · rw [getElem!_neg tbl_bytes i (by simp [tbl_bytes]; omega)]; decide

attribute [local grind =] StaticPre
local grind_pattern slot_isSome => Std.ExtHashMap.sep Host.Image (Std.ExtHashMap.sep (Mem.Blocks [(a, 8)]) R) m, m.loadInt a 8
local grind_pattern loadInt_tbl => Std.ExtHashMap.sep Host.Image F m, m.loadInt ((label "tbl").toBitVec + x + 0#64) 1
local grind_pattern tbl_entry_lt => BitVec.ofNat 64 (tbl_bytes[i]! : UInt8).toNat

theorem outer_spec [Host] [FunDecls] [Embeds inner_body]
    (hg : FunDecls.at (label "inner") = some ⟨inner_body⟩) (R : DataMem → Prop) (d : MachineData)
    (hx : (d.regs.get64 .rdi).toNat < 16)
    (h_mem : StaticPre (Mem.Blocks [(slot d, 8)] ⋆ R) d) :
    WP.wp outer_body
      (fun _ t => t.regs.get64 .rax = tbl (tbl (d.regs.get64 .rdi))
        ∧ StaticPost (Mem.Blocks [(slot d, 8)] ⋆ R) t)
      (fun _ _ => False) d := by
  have hcall := Program.WP.callSpec_of_triple hg (inner_spec R)
  refine Program.WP.cfg (fun
      | .entry, t | .label "outer", t => t = d
      | .exit, t => t.regs.get64 .rax = tbl (tbl (d.regs.get64 .rdi))
          ∧ StaticPost (Mem.Blocks [(slot d, 8)] ⋆ R) t
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 [hcall] with finish

end Kraken.Examples.StaticCall
