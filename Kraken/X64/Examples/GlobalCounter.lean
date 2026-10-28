module

public import Kraken.StateCfg
public import Kraken.X64.WP.Writable
import Kraken.X64.Parser
import all Kraken.SeparationMem

/-!
# A writable global

```
counter_inc:                   ; counter += 1
    lea     rcx, [rip + counter]
    mov     eax, dword ptr [rcx]
    add     rax, 1
    mov     dword ptr [rcx], eax
    ret
    .align 4
counter:                       ; static unsigned counter; (in .bss)
    .zero 4
```

The counter is a 32-bit global in `.bss`, written `.zero 4`. The label
`counter` is writable (the local `Host.Writable` instance), so its cell is in
`Host.ImageRW`.

`counter_inc_spec_bytes`: entered by a call with the counter's cell holding
`v` and the return slot owned, `counter_inc` returns to the caller with the
cell holding `v + 1` (modulo `2 ^ 32`). The slot is owned in the frame, as in
`StaticCall`: the store to the counter must be seen to miss the return address.

`counter_inc_spec`: on the writable image as loaded (`Host.ImageRW`), the cell
holds zero; `Host.ImageRW.split` takes it out, and the postcondition states the
cell's new bytes, `1`, beside the rest of the writable image
(`Host.ImageRWExcept`).
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.GlobalCounter

def counter_body : Program := parse("
counter_inc:
    lea counter(%rip),%rcx
    mov (%rcx),%eax
    add $1,%rax
    mov %eax,(%rcx)
    ret
    .align 4
counter:
    .zero 4
")

/-- The counter is writable data. -/
local instance writable [Host] : Host.Writable := ⟨["counter"]⟩

/-- The address of the counter. -/
abbrev counter [Host] : BitVec 64 := (label "counter").toBitVec

/-- The address of the counter, as `kvcgen64` leaves it: base plus zero displacement. -/
theorem add_ofInt_zero (x : BitVec 64) : x + BitVec.ofInt 64 (Int64.toInt 0) = x := by
  simp

/-- The 32-bit counter read back from its bytes. -/
theorem ofInt_ofBytes_toBytes_32 (v : Int) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v)) = BitVec.ofInt 32 v :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl v

/-- The low half of the 64-bit increment is the 32-bit increment. -/
theorem take_one_add_setWidth (v : BitVec 32) : (1#64 + BitVec.setWidth 64 v).take 32 = v + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

/-- The return slot of a call made in state `s`. -/
abbrev slot (s : MachineData) : BitVec 64 := s.regs.get64 .rsp - 8#64

/-- A store of 8 bytes into an 8-byte block of the frame: the block now holds them. -/
theorem block_storeInt {m : DataMem} {a : BitVec 64} {G F : DataMem → Prop}
    (h : m =⋆ G ⋆ (Mem.Blocks [(a, 8)] ⋆ F)) (v : Int) :
    Mem.storeInt m a 8 v =⋆ G ⋆ (Mem.Bytes a (Int.toBytes 8 v) ⋆ F) := by
  rw [Std.ExtHashMap.sep_comm_l] at h ⊢
  obtain ⟨m1, m2, hu, hi, ⟨_, bs, hlen, rfl⟩, hF⟩ := h
  exact Mem.storeInt_sep a 8 bs _ m ⟨⟨_, m2, hu, hi, rfl, hF⟩, hlen⟩ v

/-- Owned bytes are a block of their length. -/
theorem bytes_block {m : DataMem} {a : BitVec 64} {bs : List UInt8} {G F : DataMem → Prop}
    (h : m =⋆ G ⋆ (Mem.Bytes a bs ⋆ F)) (hlen : bs.length = 8) :
    m =⋆ G ⋆ (Mem.Blocks [(a, 8)] ⋆ F) := by
  rw [Std.ExtHashMap.sep_comm_l] at h ⊢
  exact Mem.Block.sep_intro hlen (by decide) h

/-- Owned bytes load back. -/
theorem bytes_loadInt {m : DataMem} {a : BitVec 64} {bs : List UInt8} {G F : DataMem → Prop}
    (h : m =⋆ G ⋆ (Mem.Bytes a bs ⋆ F)) (hlen : bs.length = 8) :
    Mem.loadInt m a 8 = some (Int.ofBytes bs) := by
  rw [Std.ExtHashMap.sep_comm_l] at h
  exact Mem.loadInt_sep bs a 8 _ m h hlen (by decide)

attribute [local grind =] add_ofInt_zero ofInt_ofBytes_toBytes_32 BitVec.ofInt_toInt
  take_one_add_setWidth

theorem counter_inc_spec_bytes [Host] [FunDecls] [Embeds counter_body] (s : MachineData)
    (ra : Int64) (v : BitVec 32) (R : DataMem → Prop) :
    ⦃ fun t => t = s.pushRa ra
        ∧ s.dmem =⋆ Host.ImageAt "counter" (Int.toBytes 4 v.toInt) ⋆ (Mem.Blocks [(slot s, 8)] ⋆ R) ⦄
      counter_body
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
      ∧ t.dmem =⋆ Host.ImageAt "counter" (Int.toBytes 4 (v + 1).toInt) ⋆ (Mem.Blocks [(slot s, 8)] ⋆ R) ⦄ := by
  refine ⟨fun t₀ ⟨h₀, hmem⟩ => ?_⟩
  subst h₀
  have hlen : (Int.toBytes 4 v.toInt).length = 4 := Int.toBytes_length _ _
  have hlen8 : (Int.toBytes 8 ra.toBitVec.toInt).length = 8 := Int.toBytes_length _ _
  -- after the push, the slot holds the return address
  have hpush : (s.pushRa ra).dmem =⋆ Host.ImageAt "counter" (Int.toBytes 4 v.toInt)
      ⋆ (Mem.Bytes (slot s) (Int.toBytes 8 ra.toBitVec.toInt) ⋆ R) := block_storeInt hmem _
  have hload := Host.ImageAt.loadInt hpush hlen (by decide)
  -- after the store, the counter holds `x` and the slot still holds the return address
  have hstore (x : Int) := Host.ImageAt.storeInt hpush hlen x
  have hpost (x : Int) := bytes_block (hstore x) hlen8
  have hret (x : Int) := bytes_loadInt (hstore x) hlen8
  refine Program.WP.cfg (fun
      | .entry, t | .label "counter_inc", t => t = s.pushRa ra
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- The counter's cell as loaded: four zero bytes (`.zero 4`). -/
def zero4 : List UInt8 := [0, 0, 0, 0]

/-- The counter's cell is a cell of the image. -/
theorem counter_cell [Host] [he : Embeds counter_body] :
    ((label "counter").toBitVec, zero4) ∈ Host.dataCells :=
  Host.dataCells_mem he.embedding.isInfixAt (i := 7) rfl rfl

theorem counter_inc_spec [Host] [FunDecls] [he : Embeds counter_body] (s : MachineData)
    (ra : Int64) (R : DataMem → Prop) :
    ⦃ fun t => t = s.pushRa ra ∧ s.dmem =⋆ Host.ImageRW ⋆ (Mem.Blocks [(slot s, 8)] ⋆ R) ⦄
      counter_body
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
      ∧ t.dmem =⋆ Host.ImageAt "counter" (Int.toBytes 4 1)
          ⋆ (Host.ImageRWExcept "counter" zero4 ⋆ (Mem.Blocks [(slot s, 8)] ⋆ R)) ⦄ := by
  refine ⟨fun t₀ ⟨h₀, hmem⟩ => ?_⟩
  rw [Host.ImageRW.split counter_cell List.mem_cons_self,
    Std.ExtHashMap.sep_comm_l (p := Host.ImageRWExcept _ _)] at hmem
  have h := (counter_inc_spec_bytes s ra 0 (Host.ImageRWExcept "counter" zero4 ⋆ R)).1 t₀
    ⟨h₀, hmem⟩
  refine Program.wp_mono (fun _ h => h) ?_ h
  intro u ⟨ha, hrsp, hm⟩
  refine ⟨ha, hrsp, ?_⟩
  rw [Std.ExtHashMap.sep_comm_l (p := Host.ImageRWExcept _ _)]
  exact hm

end Kraken.Examples.GlobalCounter
