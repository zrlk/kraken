import Kraken.EnvVCGen
import Kraken.X64.Parser

/-!
# `vcgen` over the environment wp: the stack and `jmp *d(%b)` on shared locations

`stackShared` pushes a register and pops it into another with the stack slot
outside `dmem`, and `jmpShared` jumps through a shared 8-byte table entry. Each
is one `vcgen` call in `SharedEnv.lastWrite` with the combined rules
(`push_reg_env_spec`, `pop_reg_env_spec`, `jmp_mem_base_disp_env_spec`,
registered): the slot is read back from the environment state the store left.
-/

open Std.WP
open Kraken
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

section

open Kraken.X64.Parser

variable [layout : _root_.Layout]

/-- A push and a pop through a shared stack slot. -/
def stackShared : Program := parse("
  pushq %rdi
  popq %rax
")

local instance stackShared.env : CodeEnv := ⟨layout stackShared⟩

theorem stackShared_correctEnv (d : MachineData)
    (h_slot : Mem.loadInt d.dmem (d.regs.get64 .rsp - 8) 8 = none) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.get64 .rsp - 8, 8)])
      (fun s _ => s = d)
      stackShared
      (fun s _ => s.regs.get64 .rax = d.regs.get64 .rdi ∧ s.regs.get64 .rsp = d.regs.get64 .rsp)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold stackShared
  vcgen
  all_goals subst_vars
  all_goals simp_all [SharedEnv.lastWrite, SharedEnv.upd, and_assoc, BitVec.setWidth_setWidth_of_le]

end

section

open Kraken.X64.Parser

variable [layout : _root_.Layout]

/-- An indirect jump through a shared table entry. -/
def jmpShared : Program := parse("
  jmpq *8(%rdi)
")

local instance jmpShared.env : CodeEnv := ⟨layout jmpShared⟩

theorem jmpShared_correctEnv (d : MachineData) (g₀ : BitVec 64 → BitVec 128)
    (h_ent : Mem.loadInt d.dmem (d.regs.get64 .rdi + 8) 8 = none) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.get64 .rdi + 8, 8)])
      (fun s g => s = d ∧ g = g₀)
      jmpShared
      (fun _ _ => False)
      (fun a s _ => s = d ∧ a = Int64.ofBitVec ((g₀ (d.regs.get64 .rdi + 8)).setWidth 64)) := by
  apply TripleEnv.of_triple
  unfold jmpShared
  vcgen
  all_goals obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
  all_goals simp_all [SharedEnv.lastWrite, and_assoc]

end
