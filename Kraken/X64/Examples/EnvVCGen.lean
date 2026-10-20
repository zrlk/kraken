import Kraken.EnvVCGen
import Kraken.X64.Parser
import Kraken.SeparationMem

/-!
# `vcgen` over the environment wp: a mixed program

`fetchAddStash` mixes register arithmetic, a shared counter, and a private
slot: `lock xaddq` fetches-and-increments the shared counter at `(%rdi)`, the
old value plus one is stored to the private slot at `(%rsi)` (in `dmem`) and
read back, and the counter is read once more by a plain `movq`. One `vcgen`
call proves it in `SharedEnv.lastWrite [(counter, 8)]`:

- `movq $1, %rax` and `addq $1, %rax` by the generic rule
  (`MachineWP.env_lift_spec`, i.e. the `MachineWP` register rules);
- `lock xaddq` by `MachineWP.lock_xadd_shared_spec`;
- the three plain moves by the combined rules (`mov_store_env_spec`,
  `mov_load_env_spec`): the store and the first load hit `dmem`, the second
  load the environment, the same rule for both loads.
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

open Kraken.X64.Parser

variable [layout : _root_.Layout]

/-- Fetch-and-increment a shared counter, stash the new value privately, read
it back, and re-read the counter. -/
def fetchAddStash : Program := parse("
  movq $1, %rax
  lock xaddq %rax, (%rdi)
  addq $1, %rax
  movq %rax, (%rsi)
  movq (%rsi), %rcx
  movq (%rdi), %rdx
")

local instance fetchAddStash.env : CodeEnv := ⟨layout fetchAddStash⟩

/-- From counter value `v` (shared: not in `dmem`) and a mapped private slot:
`rax` and `rcx` end with `v + 1`, `rdx` re-reads the counter, which now holds
`v + 1`. -/
theorem fetchAddStash_correctEnv (d : MachineData) (v : BitVec 64) (w : Int)
    (h_none : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 = none)
    (h_slot : Mem.loadInt d.dmem (d.regs.get64 .rsi) 8 = some w) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.get64 .rdi, 8)])
      (fun s g => s = d ∧ (g (d.regs.get64 .rdi)).setWidth 64 = v)
      fetchAddStash
      (fun s g => s.regs.get64 .rax = v + 1 ∧ s.regs.get64 .rcx = v + 1 ∧
        s.regs.get64 .rdx = v + 1 ∧ (g (d.regs.get64 .rdi)).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  have h_rt : ∀ (m : DataMem) (a : BitVec 64) (x : Int),
      Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
    fun m a x => Mem.loadInt_storeInt m a 8 x (by decide)
  have h_keep : ∀ x : Int,
      Mem.loadInt (Mem.storeInt d.dmem (d.regs.get64 .rsi) 8 x) (d.regs.get64 .rdi) 8 = none :=
    fun _ => loadInt_storeInt_of_none (by rw [h_slot]; rfl) h_none
  apply TripleEnv.of_triple
  unfold fetchAddStash
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, rmwOp128, BitVec.ofInt_ofBytes_toBytes, -BitVec.toInt_add,
    -BitVec.toInt_ofInt, and_assoc, BitVec.add_comm]

/-! ## A byte flag and a `lock inc`

`incFlag` increments a shared counter at `(%rdi)` with `lock incq`
(`lock_un_shared_spec`, registered) and raises a shared byte flag at `(%rsi)`
with `movb $1` (`mov8_store_imm_shared_spec`, passed to `vcgen`). -/

/-- Increment a shared counter, then raise a shared byte flag. -/
def incFlag : Program := parse("
  lock incq (%rdi)
  movb $1, (%rsi)
")

local instance incFlag.env : CodeEnv := ⟨layout incFlag⟩

theorem incFlag_correctEnv (d : MachineData) (v : BitVec 64)
    (h_ctr : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 = none)
    (h_flag : Mem.loadInt d.dmem (d.regs.get64 .rsi) 1 = none) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.get64 .rdi, 8), (d.regs.get64 .rsi, 1)])
      (fun s g => s = d ∧ (g (d.regs.get64 .rdi)).setWidth 64 = v)
      incFlag
      (fun _ g => (g (d.regs.get64 .rsi)).setWidth 8 = 1 ∧
        (d.regs.get64 .rsi ≠ d.regs.get64 .rdi → (g (d.regs.get64 .rdi)).setWidth 64 = v + 1))
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold incFlag
  vcgen [mov8_store_imm_shared_spec]
  all_goals simp_all [SharedEnv.lastWrite, rmwOp128, LockUnOp.eval]
  -- the counter, read past the flag's update
  intro hne
  simp [SharedEnv.upd, Ne.symm hne]

end
