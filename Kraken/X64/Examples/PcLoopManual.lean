module

public import Kraken.StateCfg
import Kraken.X64.Parser

/-!
# A loop that reads the pc, by hand

```
; rax = rdi, by counting
count:
    xor     eax, eax
.Lloop:
    lea     rcx, [rip]                ; rcx = address of the next instruction = .Lhere
.Lhere:
    test    rdi, rdi
    jz      .Ldone
    dec     rdi
    add     rax, 1
    sub     rcx, .Lhere - .Lloop      ; rcx = .Lloop (the immediate is a label difference)
    jmp     rcx                       ; back edge
.Ldone:
    ret
```

## The difficulty

`Program.wp` quantifies over every placement of a fragment, so no triple says
what `lea rcx, [rip]` puts in `rcx`, and `Program.WP.cfg` asks for a triple
of every block. The proof therefore works at the machine level (`Eventually`
over `step1 Host.exe`, as `RipJump.lean`) and does by hand what the cfg rule
does:

* **The induction.** The loop's property is an `Eventually` from `.Lloop`,
  proved by strong induction on `rdi`, threading the invariant through.
* **The placement.** Each pc-free piece of the body is a triple read back at
  its place (`Program.step1_of_wp`, the piece's `Embeds` from the body's via
  `Embeds.ofIsInfixAt`); the `lea` is stepped at its index (`lea_rip_step`).
* **The gluing.** The runs are chained with `eventually_trans`.

The pieces' triples are still `Program.WP.cfg` + `kvcgen64`. The jump back
needs `.Lloop` and `.Lhere`, and the exit `.Ldone` and `.Lhere`, at distinct
addresses (`label_ne`, from the placement).
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.PcLoopManual

def count_body : Program := parse("
count:
  xorl %eax, %eax
.Lloop:
  leaq 0(%rip), %rcx
.Lhere:
  testq %rdi, %rdi
  je .Ldone
  decq %rdi
  addq $1, %rax
  subq $.Lhere-.Lloop, %rcx
  jmp %rcx
.Ldone:
  ret
")

/-- Entry: clear `eax`. Directives 0–1. -/
def pieceA : Program := parse("
count:
  xorl %eax, %eax
")

/-- The loop body from `.Lhere`. Directives 4–10. -/
def pieceB : Program := parse("
.Lhere:
  testq %rdi, %rdi
  je .Ldone
  decq %rdi
  addq $1, %rax
  subq $.Lhere-.Lloop, %rcx
  jmp %rcx
")

/-- `.Ldone`: the return. Directives 11–12. -/
def pieceC : Program := parse("
.Ldone:
  ret
")

theorem pieceA_infix : pieceA.IsInfixAt count_body 0 := ⟨_, rfl⟩
theorem pieceB_infix : pieceB.IsInfixAt count_body 4 := ⟨_, rfl⟩
theorem pieceC_infix : pieceC.IsInfixAt count_body 11 := ⟨_, rfl⟩

/-- Two labels of the body with an instruction between them sit at different
addresses. -/
theorem label_ne [Host] {k : Nat} (hk : count_body.IsInfixAt Host.prog k) {i m j : Nat}
    {l l' : Label} {ins : Instr} (hi : count_body[i]? = some (.label l))
    (hj : count_body[j]? = some (.label l')) (hm : count_body[m]? = some (.instr ins))
    (hpad : ¬ ins.IsPadding) (him : i ≤ m) (hmj : m < j) : label l ≠ label l' := by
  rw [Host.label_eq hk hi, Host.label_eq hk hj]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hm
  exact Host.addrOf_ne (m := k + m)
    ((List.isInfixAt_iff_getElem?.mp hk m hlt).trans ((List.getElem?_eq_getElem hlt).symm.trans hm))
    hpad (by omega) (by omega)

/-- A label takes no space: the next index has its address. -/
theorem addrOf_succ_label [Host] {j : Nat} {l : Label} (hj : Host.prog[j]? = some (.label l)) :
    Host.addrOf (j + 1) = Host.addrOf j := by
  rw [Host.addrOf_succ hj, Host.label_size _ l hj]
  simp

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

/-- The back edge: `rcx = .Lhere`, minus `.Lhere - .Lloop`, is `.Lloop`. -/
theorem back_edge {rcx : BitVec 64} {a b : Int64} (h : rcx = a.toBitVec) :
    Int64.ofBitVec (rcx - BitVec.setWidth 64 (a - b).toBitVec) = b := by
  apply Int64.toBitVec_inj.mp
  rw [Int64.toBitVec_ofBitVec, BitVec.setWidth_eq, Int64.toBitVec_sub, h]
  bv_omega

attribute [local grind =] back_edge

/-- The loop invariant: what is counted plus what is left is the argument, and
the stack and memory are as on entry `t₀`. -/
abbrev Inv (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rax + s.regs.get64 .rdi = t₀.regs.get64 .rdi
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = t₀.dmem

/-- At `.Ldone`: the count is the argument. -/
abbrev Done (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rax = t₀.regs.get64 .rdi
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = t₀.dmem

theorem pieceA_spec [Host] [FunDecls] (t₀ : MachineData) :
    ⦃ fun t => t = t₀ ⦄ pieceA ⦃ fun _ t => Inv t₀ t; (fun _ _ => False) ⦄ := by
  refine ⟨fun t h₀ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, u | .label "count", u => u = t
      | .exit, u => Inv t u
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem pieceB_spec [Host] [FunDecls] (t₀ : MachineData) (n : Nat)
    (h1 : label ".Lloop" ≠ label ".Lhere") (h2 : label ".Ldone" ≠ label ".Lhere") :
    ⦃ fun s => Inv t₀ s ∧ s.regs.get64 .rcx = (label ".Lhere").toBitVec
        ∧ (s.regs.get64 .rdi).toNat = n ⦄
      pieceB
    ⦃ (fun _ _ => False); fun a s => (a = label ".Ldone" ∧ Done t₀ s)
        ∨ (a = label ".Lloop" ∧ Inv t₀ s ∧ (s.regs.get64 .rdi).toNat < n) ⦄ := by
  refine ⟨fun t h₀ => ?_⟩
  refine Program.WP.cfg (fun
      | .entry, u | .label ".Lhere", u => u = t
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem pieceC_spec [Host] [FunDecls] (s : MachineData) (ra : Int64) :
    ⦃ fun t => Done (s.pushRa ra) t ⦄
      pieceC
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = (s.pushRa ra).dmem
      ∧ t.regs.get64 .rax = (s.pushRa ra).regs.get64 .rdi ⦄ := by
  refine ⟨fun t₀ h₀ => ?_⟩
  refine Program.WP.cfg (fun
      | .entry, u | .label ".Ldone", u => u = t₀
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- Entered with `ra` on the stack, `count` runs to `ra` with `rax` the
argument, the stack popped and the memory unchanged. -/
theorem count_spec [Host] [FunDecls] [he : Embeds count_body] (s : MachineData) (ra : Int64) :
    Eventually (step1 Host.exe)
      (fun u => u.pc = ra ∧ u.data.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8
        ∧ u.data.dmem = (s.pushRa ra).dmem
        ∧ u.data.regs.get64 .rax = (s.pushRa ra).regs.get64 .rdi)
      ⟨s.pushRa ra, label "count"⟩ := by
  have hk := he.embedding.isInfixAt
  generalize ht₀ : s.pushRa ra = t₀ at *
  have hLloop : label ".Lloop" = Host.addrOf (he.embedding.start + 2) := Host.label_eq hk (i := 2) rfl
  have hLhere : label ".Lhere" = Host.addrOf (he.embedding.start + 4) := Host.label_eq hk (i := 4) rfl
  have hLdone : label ".Ldone" = Host.addrOf (he.embedding.start + 11) :=
    Host.label_eq hk (i := 11) rfl
  have h1 : label ".Lloop" ≠ label ".Lhere" := label_ne hk (i := 2) (m := 3) (j := 4) rfl rfl rfl
    (by rintro ⟨⟩) (by omega) (by omega)
  have h2 : label ".Lhere" ≠ label ".Ldone" := label_ne hk (i := 4) (m := 5) (j := 11) rfl rfl rfl
    (by rintro ⟨⟩) (by omega) (by omega)
  -- the loop, from `.Lloop`, by strong induction on what is left in `rdi`
  have loop : ∀ n u, (u.regs.get64 .rdi).toNat = n → Inv t₀ u →
      Eventually (step1 Host.exe)
        (fun u => u.pc = ra ∧ u.data.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
          ∧ u.data.dmem = t₀.dmem ∧ u.data.regs.get64 .rax = t₀.regs.get64 .rdi)
        ⟨u, label ".Lloop"⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro u hn hinv
    -- `.Lloop`: the pc read, stepped at its index
    rw [hLloop, ← addrOf_succ_label (l := ".Lloop")
      ((List.isInfixAt_iff_getElem?.mp hk 2 (by decide)).trans rfl)]
    refine .step _ _ (lea_rip_step (j := he.embedding.start + 2 + 1)
      ((List.isInfixAt_iff_getElem?.mp hk 3 (by decide)).trans rfl) u) ?_
    rintro _ rfl
    -- `.Lhere`: out to `.Ldone`, or back to `.Lloop` with less left
    refine eventually_trans _ _ _ _
      (@Program.step1_of_wp _ _ _ (he.ofIsInfixAt pieceB_infix) _ _ _
        (fun v => (v.pc = label ".Ldone" ∧ Done t₀ v.data)
          ∨ (v.pc = label ".Lloop" ∧ Inv t₀ v.data ∧ (v.data.regs.get64 .rdi).toNat < n))
        ((pieceB_spec t₀ n h1 (Ne.symm h2)).1 _ ⟨?_, ?_, ?_⟩) (fun _ _ h => h.elim) (fun _ h => h)) ?_
    · simpa [Inv] using hinv
    · simp [hLhere]
    · simpa using hn
    rintro ⟨v, pc⟩ (⟨hpc, hd⟩ | ⟨hpc, hinv', hlt⟩) <;> dsimp only at hpc <;> subst hpc
    · -- out: `.Ldone`
      rw [hLdone]
      subst ht₀
      exact @Program.step1_of_wp _ _ _ (he.ofIsInfixAt pieceC_infix) _ _ _ _
        ((pieceC_spec s ra).1 _ hd) (fun _ _ h => h.elim) (fun _ h => h)
    · -- back: `.Lloop`, with less left
      exact ih _ hlt v rfl hinv'
  -- `count`: clear `eax`, fall into the loop
  rw [Host.label_eq hk (i := 0) rfl]
  refine eventually_trans _ _ _ _
    (@Program.step1_of_wp _ _ _ (he.ofIsInfixAt pieceA_infix) _ _ _
      (fun v => v.pc = Host.addrOf (he.embedding.start + 2) ∧ Inv t₀ v.data)
      ((pieceA_spec t₀).1 _ rfl) (fun u hu h => ⟨hu, h⟩) (fun _ h => h.elim)) ?_
  rintro ⟨v, pc⟩ ⟨hpc, hinv⟩
  dsimp only at hpc hinv
  subst hpc
  rw [← hLloop]
  exact loop _ v rfl hinv

end Kraken.Examples.PcLoopManual
