module

public import Kraken.StateCfg
public import Kraken.X64.WP.Image
import Kraken.X64.Parser

/-!
# A jump table

`sel` is what clang `-O2` emits for

```c
int sel(unsigned x) {
  switch (x) { case 0: return 10; case 1: return 20; case 2: return 30; default: return 0; }
}
```

In Intel syntax (the body below is its AT&T transcription; Kraken's parser
reads AT&T):

```
sel:
    cmp     edi, 2
    ja      .Ldefault
    mov     eax, edi                          ; zero-extends x into rax
    lea     rcx, [rip + .LJTI0_0]             ; table base
    movsxd  rax, dword ptr [rcx + 4*rax]      ; entry = case label - table base
    add     rax, rcx                          ; absolute target
    jmp     rax
.Lcase0:
    mov     eax, 10
    ret
.Lcase1:
    mov     eax, 20
    ret
.Lcase2:
    mov     eax, 30
    ret
.Ldefault:
    xor     eax, eax
    ret

    .section .rodata
    .p2align 2
.LJTI0_0:
    .long   .Lcase0 - .LJTI0_0
    .long   .Lcase1 - .LJTI0_0
    .long   .Lcase2 - .LJTI0_0
```

`sel_spec`: entered with a return address on the stack (at `s.pushRa ra`) and
the program's image loaded, `sel` returns to it with `eax = selFn x`
(zero-extended into `rax`), the stack popped and the memory unchanged.

The table is part of the program: its entries are `.long` data words whose
values are label differences, kept symbolic (`Directive.word`). Here it sits
in the text behind the code, aligned to 4, where the compiler's output has it
in `.rodata`. The precondition says only that the image is loaded
(`Host.Image`); `Host.word_value` reads each entry back from it. The one
assumption about the table is that each offset fits in 32 bits (`h_fits`),
which the assembler checks when it fills in the relocations.
`sel_spec_of_table` is the earlier form, which assumes the three entries in
memory (`JumpTable`) instead of the image.

## Findings

* With the table in the precondition, a jump table is ordinary code for
  `Program.wp`: the pc is read only through a label (`lea .LJTI0_0(%rip)`).
* The computed jump exits at `.LJTI0_0 + sext entry`. `JumpTable` turns that
  into the address of `.Lcase_x` (`target_eq`). The cfg rule reads an exit to
  an address as a jump to every label at that address, so the proof shows
  first that the five labels have distinct addresses (`label_ne`, from the
  placement).
* The `movsxd` address depends on `x`, so the dispatch block splits on
  `x ∈ {0, 1, 2}` by hand after the bounds check, as before. The case blocks
  and the out-of-range branch are `kvcgen64 with finish`.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.JumpTable

def sel_body : Program := parse("
sel:
  cmpl $2, %edi
  ja .Ldefault
  movl %edi, %eax
  leaq .LJTI0_0(%rip), %rcx
  movslq (%rcx,%rax,4), %rax
  addq %rcx, %rax
  jmp %rax
.Lcase0:
  movl $10, %eax
  ret
.Lcase1:
  movl $20, %eax
  ret
.Lcase2:
  movl $30, %eax
  ret
.Ldefault:
  xorl %eax, %eax
  ret
  .align 4
.LJTI0_0:
  .long .Lcase0 - .LJTI0_0
  .long .Lcase1 - .LJTI0_0
  .long .Lcase2 - .LJTI0_0
")

/-- The C function. -/
def selFn (x : BitVec 32) : BitVec 32 :=
  if x = 0 then 10 else if x = 1 then 20 else if x = 2 then 30 else 0

attribute [local grind =] selFn

/-- Entry `k` of the table: the 4 bytes at `.LJTI0_0 + 4k`, sign-extended and
added to the table's address, give `target`'s address. -/
def Entry [Host] (m : DataMem) (k : Nat) (target : Label) : Prop :=
  ∃ e, Mem.loadInt m ((label ".LJTI0_0").toBitVec + BitVec.ofNat 64 k * BitVec.ofNat 64 4) 4
      = some e
    ∧ (BitVec.ofInt 32 e).signExtend 64 + (label ".LJTI0_0").toBitVec = (label target).toBitVec

/-- The table, as the loader leaves it in memory. -/
def JumpTable [Host] (m : DataMem) : Prop :=
  Entry m 0 ".Lcase0" ∧ Entry m 1 ".Lcase1" ∧ Entry m 2 ".Lcase2"

/-- The argument: the low 32 bits of `rdi`, spelled as the 32-bit rules read them. -/
abbrev arg (t : MachineData) : BitVec 32 := (t.regs.get64 .rdi).take 32

/-- Two labels of the body with an instruction between them have different
addresses. -/
theorem label_ne [Host] {k : Nat} (hk : sel_body.IsInfixAt Host.prog k) {i m j : Nat}
    {l l' : Label} {ins : Instr} (hi : sel_body[i]? = some (.label l))
    (hj : sel_body[j]? = some (.label l')) (hm : sel_body[m]? = some (.instr ins))
    (hpad : ¬ ins.IsPadding) (him : i ≤ m) (hmj : m < j) : label l ≠ label l' := by
  rw [Host.label_eq hk hi, Host.label_eq hk hj]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hm
  exact Host.addrOf_ne (m := k + m)
    ((List.isInfixAt_iff_getElem?.mp hk m hlt).trans ((List.getElem?_eq_getElem hlt).symm.trans hm))
    hpad (by omega) (by omega)

theorem sel_spec_of_table [Host] [FunDecls] [he : Embeds sel_body] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ JumpTable t.dmem ⦄
      sel_body
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = (s.pushRa ra).dmem
      ∧ t.regs.get64 .rax = (selFn (arg (s.pushRa ra))).setWidth 64 ⦄ := by
  have hk := he.embedding.isInfixAt
  generalize he.embedding.start = k at hk
  have h01 : label "sel" ≠ label ".Lcase0" := label_ne hk (i := 0) (j := 8) (m := 1) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h02 : label "sel" ≠ label ".Lcase1" := label_ne hk (i := 0) (j := 11) (m := 1) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h03 : label "sel" ≠ label ".Lcase2" := label_ne hk (i := 0) (j := 14) (m := 1) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h04 : label "sel" ≠ label ".Ldefault" := label_ne hk (i := 0) (j := 17) (m := 1) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h12 : label ".Lcase0" ≠ label ".Lcase1" := label_ne hk (i := 8) (j := 11) (m := 9) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h13 : label ".Lcase0" ≠ label ".Lcase2" := label_ne hk (i := 8) (j := 14) (m := 9) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h14 : label ".Lcase0" ≠ label ".Ldefault" := label_ne hk (i := 8) (j := 17) (m := 9) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h23 : label ".Lcase1" ≠ label ".Lcase2" := label_ne hk (i := 11) (j := 14) (m := 12) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h24 : label ".Lcase1" ≠ label ".Ldefault" := label_ne hk (i := 11) (j := 17) (m := 12) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h34 : label ".Lcase2" ≠ label ".Ldefault" := label_ne hk (i := 14) (j := 17) (m := 15) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h05 : label "sel" ≠ label ".LJTI0_0" := label_ne hk (i := 0) (j := 21) (m := 1) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h15 : label ".Lcase0" ≠ label ".LJTI0_0" := label_ne hk (i := 8) (j := 21) (m := 9) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h25 : label ".Lcase1" ≠ label ".LJTI0_0" := label_ne hk (i := 11) (j := 21) (m := 12) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h35 : label ".Lcase2" ≠ label ".LJTI0_0" := label_ne hk (i := 14) (j := 21) (m := 15) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  have h45 : label ".Ldefault" ≠ label ".LJTI0_0" := label_ne hk (i := 17) (j := 21) (m := 18) rfl rfl rfl (by rintro ⟨⟩) (by omega) (by omega)
  refine ⟨fun t₀ ⟨h₀, htab⟩ => ?_⟩
  subst h₀
  obtain ⟨⟨e0, h0l, h0t⟩, ⟨e1, h1l, h1t⟩, ⟨e2, h2l, h2t⟩⟩ := htab
  -- the dispatch reads the entry at `x`: split on `x` first
  have hx : arg (s.pushRa ra) = 0 ∨ arg (s.pushRa ra) = 1 ∨ arg (s.pushRa ra) = 2
      ∨ 2 < arg (s.pushRa ra) := by
    generalize arg (s.pushRa ra) = x
    rcases Nat.lt_or_ge x.toNat 3 with h | h
    · have : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 := by omega
      rcases this with h | h | h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
      · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
      · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
    · exact Or.inr (Or.inr (Or.inr (BitVec.lt_def.mpr (by simp; omega))))
  simp only [arg] at hx
  rcases hx with hx | hx | hx | hx <;>
  refine Program.WP.cfg (fun
      | .entry, t | .label "sel", t => t = s.pushRa ra
      | .label ".Lcase0", t => arg (s.pushRa ra) = 0 ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp
          ∧ t.dmem = (s.pushRa ra).dmem
      | .label ".Lcase1", t => arg (s.pushRa ra) = 1 ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp
          ∧ t.dmem = (s.pushRa ra).dmem
      | .label ".Lcase2", t => arg (s.pushRa ra) = 2 ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp
          ∧ t.dmem = (s.pushRa ra).dmem
      | .label ".Ldefault", t => 2 < arg (s.pushRa ra) ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp
          ∧ t.dmem = (s.pushRa ra).dmem
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  <;> cfg_cases
  <;> kvcgen64 with finish

/-- The table's entries, read from the loaded image. -/
theorem jumpTable_of_image [Host] [he : Embeds sel_body] {m : DataMem} {R : DataMem → Prop}
    (h : m =⋆ Host.Image ⋆ R)
    (h_fits : ∀ c ∈ [".Lcase0", ".Lcase1", ".Lcase2"],
      -2 ^ 31 ≤ (label c - label ".LJTI0_0").toInt ∧ (label c - label ".LJTI0_0").toInt < 2 ^ 31) :
    JumpTable m := by
  have hk := he.embedding.isInfixAt
  have hpre : ∀ j, j ≤ 2 → ∀ j' < j, ∃ e, sel_body[21 + 1 + j']? = some (.word .W32 e) := by
    intro j hj j' hj'
    rcases j' with _ | _ | j' <;> first | exact ⟨_, rfl⟩ | omega
  obtain ⟨v0, h0l, h0t⟩ := Host.word_value h hk (i := 21) (j := 0) rfl (hpre 0 (by omega)) rfl
    (h_fits _ (by simp))
  obtain ⟨v1, h1l, h1t⟩ := Host.word_value h hk (i := 21) (j := 1) rfl (hpre 1 (by omega)) rfl
    (h_fits _ (by simp))
  obtain ⟨v2, h2l, h2t⟩ := Host.word_value h hk (i := 21) (j := 2) rfl (hpre 2 (by omega)) rfl
    (h_fits _ (by simp))
  exact ⟨⟨v0, h0l, h0t⟩, ⟨v1, h1l, h1t⟩, ⟨v2, h2l, h2t⟩⟩

theorem sel_spec [Host] [FunDecls] [he : Embeds sel_body] (s : MachineData) (ra : Int64)
    (R : DataMem → Prop)
    (h_fits : ∀ c ∈ [".Lcase0", ".Lcase1", ".Lcase2"],
      -2 ^ 31 ≤ (label c - label ".LJTI0_0").toInt ∧ (label c - label ".LJTI0_0").toInt < 2 ^ 31) :
    ⦃ fun t => t = s.pushRa ra ∧ t.dmem =⋆ Host.Image ⋆ R ⦄
      sel_body
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ t.regs.get64 .rsp = (s.pushRa ra).regs.get64 .rsp + 8 ∧ t.dmem = (s.pushRa ra).dmem
      ∧ t.regs.get64 .rax = (selFn (arg (s.pushRa ra))).setWidth 64 ⦄ :=
  ⟨fun t₀ ⟨h₀, himg⟩ => (sel_spec_of_table s ra).1 t₀ ⟨h₀, jumpTable_of_image himg h_fits⟩⟩

end Kraken.Examples.JumpTable
