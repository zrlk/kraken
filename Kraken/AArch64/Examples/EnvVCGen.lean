import Kraken.AArch64.EnvVCGen
import Kraken.AArch64.Parser
import Kraken.SeparationMem

/-!
# `vcgen` over the AArch64 environment wp: a mixed program

`incStash` is one attempt of an `LDAXR`/`ADD`/`STLXR` increment of a shared
counter at `[x0]`, straight-line (no `CBNZ` retry: a loop needs `cfg`, which
has no environment version yet). The incremented value is stashed in a private
slot at `[x5]` (in `dmem`) and read back, and the counter is re-read by a
plain `LDR`. One `vcgen` call proves it in `SharedEnv.lastWrite [(counter, 8)]`:

- `ADD` by the generic rule (`MachineWP.env_lift_spec`);
- `LDAXR`, `STLXR` by `ldar_shared_spec`, `stxr_shared_spec` (the store
  succeeds or fails as the environment answers);
- the `STR` and both `LDR`s by the combined rules `str_env_spec`,
  `ldr_env_spec`: the private slot hits `dmem`, the counter the environment,
  the same rule for both loads.
-/

open Std.WP
open Kraken
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- A store to bytes that are all mapped maps no new byte. -/
private theorem subDom_storeInt_of_mapped {m : Mem 64} {b : BitVec 64} {n : Nat} {v : Int}
    (hb : (m.loadInt b n).isSome = true) : Mem.SubDom (m.storeInt b n v) m := by
  intro k hk
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.union_eq, Std.ExtHashMap.mem_union_iff] at hk
  rcases hk with hk | hk
  · exact hk
  · obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hk
    rw [Int.toBytes_length] at hi
    simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff,
      List.forall_mem_map] at hb
    have := hb i (List.mem_range.mpr hi)
    rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.isSome_getElem?_iff_mem] at this
    exact this

/-- A load that fails before a store to mapped bytes fails after it. -/
private theorem loadInt_storeInt_of_none {m : Mem 64} {a b : BitVec 64} {n k : Nat} {v : Int}
    (hb : (m.loadInt b n).isSome = true) (ha : m.loadInt a k = none) :
    (m.storeInt b n v).loadInt a k = none := by
  cases h : (m.storeInt b n v).loadInt a k with
  | none => rfl
  | some x =>
    have := Mem.SubDom.loadInt_isSome (subDom_storeInt_of_mapped hb) (by rw [h]; rfl)
    rw [ha] at this
    cases this

section

open Kraken.AArch64.Parser

variable [layout : _root_.Layout]

/-- One exclusive increment attempt of `[x0]`, the new value stashed at `[x5]`
and read back, and `[x0]` re-read. -/
def incStash : Program := parseAArch64("
    ldaxr x2, [x0]
    add x3, x2, #1
    stlxr w4, x3, [x0]
    str x3, [x5]
    ldr x6, [x5]
    ldr x7, [x0]
")

local instance incStash.env : CodeEnv := ⟨layout incStash⟩

theorem incStash_correctEnv (d : MachineData) (v : BitVec 64) (w : Int)
    (h_none : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none)
    (h_slot : Mem.loadInt d.dmem d.regs.X5.toBitVec 8 = some w) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 8)])
      (fun s g => s = d ∧ (g d.regs.X0.toBitVec).setWidth 64 = v)
      incStash
      (fun s g => s.regs.X6.toBitVec = v + 1 ∧
        s.regs.X7.toBitVec = (g d.regs.X0.toBitVec).setWidth 64 ∧
        ((g d.regs.X0.toBitVec).setWidth 64 = v + 1 ∨ (g d.regs.X0.toBitVec).setWidth 64 = v))
      (fun _ _ _ => False) := by
  have h_rt : ∀ (m : DataMem) (a : BitVec 64) (x : Int),
      Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
    fun m a x => Mem.loadInt_storeInt m a 8 x (by decide)
  have h_keep : ∀ x : Int,
      Mem.loadInt (Mem.storeInt d.dmem d.regs.X5.toBitVec 8 x) d.regs.X0.toBitVec 8 = none :=
    fun _ => loadInt_storeInt_of_none (by rw [h_slot]; rfl) h_none
  apply TripleEnv.of_triple
  unfold incStash
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, -BitVec.toInt_add, and_assoc]
  -- the `STLXR` outcome: the environment took the store, or refused it
  all_goals obtain ⟨-, h⟩ | ⟨-, h⟩ := ‹_ = true ∧ _ ∨ _ = false ∧ _› <;> subst h <;> simp_all

/-! ## Unscaled and literal forms

`sturLdur` stores `x1` to a shared slot at `[x0, #-8]` with `STUR`, reads it
back with `LDUR`, and loads a pool constant with `LDR x3, =7`. One `vcgen`
call in `SharedEnv.lastWrite [(x0 - 8, 8)]`: `stur_env_spec`, `ldur_env_spec`
(the shared disjunct, the `dmem` one refuted by `h_none`) and
`ldr_pool_env_spec`. -/

/-- A shared-slot round trip by the unscaled forms, and a pool constant. -/
def sturLdur : Program := parseAArch64("
    stur x1, [x0, #-8]
    ldur x2, [x0, #-8]
    ldr x3, =7
")

local instance sturLdur.env : CodeEnv := ⟨layout sturLdur⟩

theorem sturLdur_correctEnv (d : MachineData)
    (h_none : Mem.loadInt d.dmem (d.regs.X0.toBitVec - 8) 8 = none) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.X0.toBitVec - 8, 8)])
      (fun s _ => s = d)
      sturLdur
      (fun s g => s.regs.X2.toBitVec = d.regs.X1.toBitVec ∧ s.regs.X3.toBitVec = 7 ∧
        (g (d.regs.X0.toBitVec - 8)).setWidth 64 = d.regs.X1.toBitVec)
      (fun _ _ _ => False) := by
  -- `#-8` arrives as the 64-bit two's complement of 8
  have h8 : d.regs.X0.toBitVec + 18446744073709551608#64 = d.regs.X0.toBitVec - 8 := by bv_omega
  apply TripleEnv.of_triple
  unfold sturLdur
  vcgen
  all_goals simp_all [SharedEnv.lastWrite]
  -- the `LDUR`: the environment's answer is the `STUR`'s value
  obtain ⟨_, ⟨rfl, rfl⟩, rfl⟩ := ‹∃ v, _›
  simp

end
