module

public import Kraken.StateCfg
import Kraken.X64.Parser

/-!
# A computed jump that reads the pc

`rip_jump` jumps forward to `start`, computes the address of `L0` from a
difference of labels and the address of `L1` (read off the pc), jumps there
through a register, and returns. `rip_jump_spec`: entered with a return
address on the stack, it runs to it, with the stack popped and the memory
unchanged.

The program is the one asked for (`mov L0-L1, %rax` / `jmp %rip(%rax)`),
made legal: x86-64 has no rip-plus-register address, `%rip` reads the address
*behind* the current instruction, and `jmp *d(%rip)` loads its target from
memory. So `%rip` is read once by `lea 0(%rip), %rcx`, which sits just before
`L1` and so yields `L1`, and the jump goes through `%rax`. A leading label
names the entry.

## Findings

* The computed jump and the label difference are position-independent:
  `jmp_reg_spec` exits at the register's value, `mov_reg_imm_label_sub_spec`
  puts `label L0 - label L1` in the register.
* *Reading the pc* is what doesn't fit. `Program.wp` quantifies over every
  placement of a fragment, so no precondition can name the value of
  `lea 0(%rip)`, and `Program.WP.cfg`'s block obligations are such triples.
  The proof therefore states the result at the machine level (`Eventually`
  over `step1 Host.exe`, as `IndirectTailCall.RunsTo`) and chains by hand:
  three pc-free pieces of the body, each a triple read back at its place
  (`Program.step1_of_wp` with the piece's `Embeds` from the body's), and the
  `lea` stepped at its index (`lea_rip_step`, from `Host.step1_addrOf`).
* `Program.WP.cfg` reads an exit to address `a` as a jump to each of the
  piece's labels at `a`, so piece B's jump to `L0` needs `L0` and `L1` at
  distinct addresses (`label_ne`, from the placement). Piece C's `ret` needs
  no such fact: it pops the stack, and the cfg rule tells it from a jump.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.RipJump

def rip_jump_body : Program := parse("
rip_jump:
  jmp start
L0:
  ret
start:
  mov $L0-L1, %rax
  lea 0(%rip), %rcx
L1:
  add %rcx, %rax
  jmp %rax
")

/-- Entry to the pc read: the forward jump, `L0`'s `ret`, the label
difference. Directives 0–5 of the body. -/
def pieceA : Program := parse("
rip_jump:
  jmp start
L0:
  ret
start:
  mov $L0-L1, %rax
")

/-- From `L1`: the add and the computed jump. Directives 7–9. -/
def pieceB : Program := parse("
L1:
  add %rcx, %rax
  jmp %rax
")

/-- `L0`: the return. Directives 2–3. -/
def pieceC : Program := parse("
L0:
  ret
")

theorem pieceA_infix : pieceA.IsInfixAt rip_jump_body 0 := ⟨_, rfl⟩
theorem pieceB_infix : pieceB.IsInfixAt rip_jump_body 7 := ⟨_, rfl⟩
theorem pieceC_infix : pieceC.IsInfixAt rip_jump_body 2 := ⟨_, rfl⟩

/-- Two labels of the body with an instruction between them sit at different
addresses. -/
theorem label_ne [Host] {k : Nat} (hk : rip_jump_body.IsInfixAt Host.prog k) {i m j : Nat}
    {l l' : Label} {ins : Instr} (hi : rip_jump_body[i]? = some (.label l))
    (hj : rip_jump_body[j]? = some (.label l')) (hm : rip_jump_body[m]? = some (.instr ins))
    (hpad : ¬ ins.IsPadding) (him : i ≤ m) (hmj : m < j) : label l ≠ label l' := by
  rw [Host.label_eq hk hi, Host.label_eq hk hj]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hm
  exact Host.addrOf_ne (m := k + m)
    ((List.isInfixAt_iff_getElem?.mp hk m hlt).trans ((List.getElem?_eq_getElem hlt).symm.trans hm))
    hpad (by omega) (by omega)

/-- The value `L0 - L1` that `mov $L0-L1, %rax` loads. -/
abbrev diff [Host] : BitVec 64 := BitVec.setWidth 64 (label "L0" - label "L1").toBitVec

theorem pieceA_spec [Host] [FunDecls] (t₀ : MachineData) :
    ⦃ fun t => t = t₀ ⦄
      pieceA
    ⦃ fun _ t => t.regs.get64 .rax = diff ∧ t.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ t.dmem = t₀.dmem;
      (fun _ _ => False) ⦄ := by
  refine ⟨fun t h₀ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, u | .label "rip_jump", u | .label "start", u => u = t
      | .exit, u => u.regs.get64 .rax = diff ∧ u.regs.get64 .rsp = t.regs.get64 .rsp ∧ u.dmem = t.dmem
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem pieceB_spec [Host] [FunDecls] (R : BitVec 64) (M : DataMem) (h : label "L0" ≠ label "L1") :
    ⦃ fun t => t.regs.get64 .rcx = (label "L1").toBitVec ∧ t.regs.get64 .rax = diff
        ∧ t.regs.get64 .rsp = R ∧ t.dmem = M ⦄
      pieceB
    ⦃ (fun _ _ => False); fun a t => a = label "L0" ∧ t.regs.get64 .rsp = R ∧ t.dmem = M ⦄ := by
  refine ⟨fun t₀ h₀ => ?_⟩
  refine Program.WP.cfg (fun
      | .entry, u | .label "L1", u => u = t₀
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem pieceC_spec [Host] [FunDecls] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp ∧ t.dmem = (s.pushRa ra).dmem ⦄
      pieceC
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = (s.pushRa ra).dmem ⦄ := by
  refine ⟨fun t₀ h₀ => ?_⟩
  refine Program.WP.cfg (fun
      | .entry, u | .label "L0", u => u = t₀
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- `lea 0(%rip), %rcx` at index `j` of the ambient program puts the address
of index `j + 1` in `rcx`. Stated at the index, not as a triple. -/
theorem lea_rip_step [Host] {j : Nat}
    (hj : Host.prog[j]? = some (.instr (.regular .W64 .W64 (.lea (.low .rcx .W64)
        { base := some .rip, idx := none, disp := .int64 0 })))) (s : MachineData) :
    step1 Host.exe ⟨s, Host.addrOf j⟩ (fun u =>
      u = ⟨{ s with regs := s.regs.set64 .rcx (Host.addrOf (j + 1)).toBitVec }, Host.addrOf (j + 1)⟩) := by
  refine Host.step1_addrOf (by rw [Host.exe_getElem?, hj]; rfl)
    (Host.instr_size_pos _ _ hj (by rintro ⟨⟩)) ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interp, ConstExpr.interp,
    MachineData.setReg, Reg64s.set_low_W64, Effects.All]
  congr 2
  congr 1
  rw [show Int64.toInt 0 = 0 from rfl, Int.add_zero, Int.add_zero]
  show BitVec.setWidth 64 _ = _
  rw [BitVec.setWidth_eq, Int64.toInt, BitVec.ofInt_toInt]

theorem rip_jump_spec [Host] [FunDecls] [he : Embeds rip_jump_body] (s : MachineData) (ra : Int64) :
    Eventually (step1 Host.exe)
      (fun u => u.pc = ra ∧ u.data.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8
        ∧ u.data.dmem = (s.pushRa ra).dmem)
      ⟨s.pushRa ra, label "rip_jump"⟩ := by
  have hk := he.embedding.isInfixAt
  have hL1 : label "L1" = Host.addrOf (he.embedding.start + 7) := Host.label_eq hk (i := 7) rfl
  have hL0 : label "L0" = Host.addrOf (he.embedding.start + 2) := Host.label_eq hk (i := 2) rfl
  have h01 : label "L0" ≠ label "L1" := label_ne hk (i := 2) (m := 3) (j := 7) rfl rfl rfl
    (by rintro ⟨⟩) (by omega) (by omega)
  rw [Host.label_eq hk (i := 0) rfl]
  -- piece A: to the pc read
  refine eventually_trans _ _ _ _
    (@Program.step1_of_wp _ _ _ (he.ofIsInfixAt pieceA_infix) _ _ _
      (fun u => u.pc = Host.addrOf (he.embedding.start + 6) ∧ u.data.regs.get64 .rax = diff
        ∧ u.data.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp ∧ u.data.dmem = (s.pushRa ra).dmem)
      ((pieceA_spec (s.pushRa ra)).1 _ rfl) (fun u hu h => ⟨hu, h⟩) (fun _ h => h.elim)) ?_
  rintro ⟨u, pc⟩ ⟨hpc, hax, hsp, hmem⟩
  dsimp only at hpc hax hsp hmem
  subst hpc
  -- the pc read
  refine .step _ _ (lea_rip_step (j := he.embedding.start + 6)
    ((List.isInfixAt_iff_getElem?.mp hk 6 (by decide)).trans rfl) u) ?_
  rintro _ rfl
  -- piece B: to `L0`
  refine eventually_trans _ _ _ _
    (@Program.step1_of_wp _ _ _ (he.ofIsInfixAt pieceB_infix) _ _ _
      (fun u => u.pc = label "L0" ∧ u.data.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp
        ∧ u.data.dmem = (s.pushRa ra).dmem)
      ((pieceB_spec _ _ h01).1 _ ⟨?_, ?_, ?_, ?_⟩) (fun _ _ h => h.elim) (fun _ h => h)) ?_
  · simp [hL1]
  · simpa using hax
  · simpa using hsp
  · exact hmem
  rintro ⟨u', pc⟩ ⟨hpc, hsp', hmem'⟩
  dsimp only at hpc hsp' hmem'
  subst hpc
  -- piece C: return
  rw [hL0]
  exact @Program.step1_of_wp _ _ _ (he.ofIsInfixAt pieceC_infix) _ _ _ _
    ((pieceC_spec s ra).1 _ ⟨hsp', hmem'⟩) (fun _ _ h => h.elim) (fun _ h => h)

end Kraken.Examples.RipJump
