import Kraken.X64.Parser
import Kraken.SysV

/-!
# `even`/`odd`: the specifications

Two mutually recursive C functions,

```c
bool odd(unsigned n);
bool even(unsigned n) { if (!n) return true;  return odd(n-1); }
bool odd(unsigned n)  { if (!n) return false; return even(n-1); }
```

compiled by clang at `-O0`, are proved correct in two separate files
(`Even.lean`, `Odd.lean`). Each proof may use the specification of *both*
procedures: the one being proved at smaller arguments, and the partner's at
smaller arguments. `Link.lean` ties the two by strong induction on `n`.

This file holds what both proofs share, in the *ghost* style: the caller's
memory `R` is a logical variable of the `ProcSpec`, fixed at the call site
with `call_proc_spec_at R`. The *existential* style is in
`EvenOddExistential/`, on the same conditions.

## What is general and what is this program's

General, in the library and used here unchanged:

* `Kraken.SysV`: the calling convention's share of any procedure's
  specification — `RetCell`, the stack reservation `Reserve` and its
  arithmetic, `SavedRegs`, `CallPre`/`CallPost`, the register conventions
  `ArgU32`/`RetU8`, and the `grind` call `grind_cells`;
* `Kraken.MachineWP`: `ProcSpec.of_cfg_post` (a procedure from its blocks),
  `call_proc_spec_at` (a call through the callee's spec), `call_simp`;
* `Kraken.SepCells`: the cell rules `grind` uses for every load and store.

This program's, below:

* the two bodies;
* `need n`: how much stack the pair uses at argument `n` — a fact about this
  compiler output, exported next to the specification;
* the frame layout clang chose (`OwnCells`, `Own`), and how `CallPre`'s
  reservation opens into it at the entry (`CallPre.cells`) and folds back at
  the exit (`CallPost.of_cells`): the cell rules match loads and stores to
  exact cells, so the own bytes are split once, in `hpre`/`hpost` of each
  proof, and the blocks name the cells at fixed address terms;
* the specifications `EvenPre`/`EvenPost`, `OddPre`/`OddPost`.

## Calling convention vs. semantics

The specification of a procedure at argument `n` is the convention's
`CallPre (need n)`/`CallPost (need n)` plus one semantic conjunct each side.

Calling convention (SysV x86-64, as the compiler relies on it; `Kraken.SysV`):

* the return address is at `[rsp]` on entry (`RetCell ra rsp`);
* the argument is in `edi` — only the low 32 bits of `rdi` (`ArgU32`);
* on return `rsp` is 8 above its entry value (the return address popped),
  and `rbx`, `rbp`, `r12`–`r15` hold their entry values;
* the stack below the entry `rsp` is the procedure's to use: the caller
  *reserves* `need n` bytes there (`Reserve (need n) rsp`), and gets them
  back as owned bytes;
* the result is in `al` (`RetU8`).

Semantics:

* the argument `n` (as a natural number; `n < 2^32` follows from its being
  the value of `edi`);
* `even` returns `(n+1) % 2`, `odd` returns `n % 2` — as a byte in `al`,
  all 8 bits of it (the `and al, 1` on both paths makes the `bool`
  well-formed, so this is more than C's `bool` promises).

## Stack depth

The reservation follows Bedrock's `reserving` clause (see `Kraken.SysV`).
Bedrock's amount is a compile-time constant; here the two procedures recurse,
so the amount is a function of the argument, `need n`, exported next to the
specification like the result is. It is about clang's `-O0` output (24 own
bytes per frame, 8 for each pushed return address), not about `even`; a
tail-calling or inlined build would export a different `need`, against the
same `EvenPre`/`EvenPost` otherwise.

## Caveats

* Kraken has no faulting model, so stack exhaustion cannot be a runtime
  error: the precondition demands the whole stack the recursion will touch,
  and a run from `CallPre` never leaves it.
* The specification is total: a run from `CallPre` *reaches* the return
  address. That is what the recursion on `n` proves.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.EvenOddGhost

/-! ## The bodies -/

/-- `even`, as clang `-O0` emits it (AT&T syntax; labels renamed for the
parser; the `ret` is kept — Kraken's `ret_spec` reads the address at `[rsp]`). -/
def even_body : Program := parse("
even:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  movl %edi, -8(%rbp)
  cmpl $0, -8(%rbp)
  jne .LBB0_2
  movb $1, -1(%rbp)
  jmp .LBB0_3
.LBB0_2:
  movl -8(%rbp), %edi
  subl $1, %edi
  call odd
  andb $1, %al
  movb %al, -1(%rbp)
.LBB0_3:
  movb -1(%rbp), %al
  andb $1, %al
  addq $16, %rsp
  popq %rbp
  ret
")

/-- `odd`: the same text with the base case returning `0` and the call going
to `even`. -/
def odd_body : Program := parse("
odd:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  movl %edi, -8(%rbp)
  cmpl $0, -8(%rbp)
  jne .LBB1_2
  movb $0, -1(%rbp)
  jmp .LBB1_3
.LBB1_2:
  movl -8(%rbp), %edi
  subl $1, %edi
  call even
  andb $1, %al
  movb %al, -1(%rbp)
.LBB1_3:
  movb -1(%rbp), %al
  andb $1, %al
  addq $16, %rsp
  popq %rbp
  ret
")

/-! ## The stack this output uses -/

/-- What `even` and `odd` reserve at argument `n`: 24 own bytes per frame
(saved `rbp`, 16 bytes of locals), and for each of the `n` nested calls the
pushed return address and the callee's frame. -/
def need (n : Nat) : Nat := 24 + 32 * n

/-- What is reserved below a procedure's own 24 bytes: `need n - 24`. -/
def below (n : Nat) : Nat := 32 * n

theorem need_eq (n : Nat) : need n = 24 + below n := rfl

theorem need_le {n : Nat} (hn : n < 2 ^ 32) : need n ≤ 2 ^ 64 := by unfold need; omega

/-- The reservation below the own bytes, at `n + 1`: the slot the call pushes
into, then the callee's reservation. The blocks open it this way at the call
(`grind` rule). -/
@[grind =] theorem Reserve_below_succ (k : Nat) (r : BitVec 64) (hk : k < 2 ^ 32) :
    Reserve (below (k + 1)) r = 8 ?@ (r - 8) ⋆ Reserve (need k) (r - 8) := by
  have e : below (k + 1) = 8 + need k := by unfold below need; omega
  rw [e, Reserve_split 8 (need k) r (by unfold need; omega)]
  rfl

/-- The procedure's own 24 bytes as the cells its code uses, in front of `X`:
the unused 8, the spilled argument, padding, the `bool` local, the saved
`rbp`. -/
abbrev OwnCells (r : BitVec 64) (X : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 24) ⋆ (4 ?@ (r - 16) ⋆ (3 ?@ (r - 12) ⋆ (1 ?@ (r - 9) ⋆ (8 ?@ (r - 8) ⋆ X))))

theorem own_cells (r : BitVec 64) (X : Mem 64 → Prop) :
    24 ?@ (r - 24) ⋆ X = OwnCells r X := by
  have h24 : (24 : Nat) = 8 + (4 + (3 + (1 + 8))) := rfl
  have e1 : r - 24 + BitVec.ofNat 64 8 = r - 16 := by bv_omega
  have e2 : r - 16 + BitVec.ofNat 64 4 = r - 12 := by bv_omega
  have e3 : r - 12 + BitVec.ofNat 64 3 = r - 9 := by bv_omega
  have e4 : r - 9 + BitVec.ofNat 64 1 = r - 8 := by bv_omega
  rw [h24, Block.split _ 8 _ (by decide), e1, Block.split _ 4 _ (by decide), e2,
    Block.split _ 3 _ (by decide), e3, Block.split _ 1 _ (by decide), e4]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The reservation in front of `X` is the cells the code uses in front of
the reservation below them. Used at a procedure's entry (`hpre`) and exit
(`hpost`) so that inside the blocks every tree names the same cells at the
same address terms (see the note on addresses in `SepCells`). Not a `grind`
rewrite: the blocks pass the callee's reservation around whole. -/
theorem Reserve_cells (n : Nat) (r : BitVec 64) (X : Mem 64 → Prop)
    (hn : need n ≤ 2 ^ 64) :
    Reserve (need n) r ⋆ X = 8 ?@ (r - 24) ⋆ (4 ?@ (r - 16) ⋆ (3 ?@ (r - 12)
      ⋆ (1 ?@ (r - 9) ⋆ (8 ?@ (r - 8) ⋆ (Reserve (below n) (r - 24) ⋆ X))))) := by
  rw [need_eq] at hn ⊢
  have e : BitVec.ofNat 64 24 = (24 : BitVec 64) := rfl
  rw [Reserve_split 24 (below n) r hn, e, Std.ExtHashMap.sep_assoc, own_cells]

/-- The procedure's own cells other than the `bool` local, in front of `X`,
as the tables of both proofs name them after the prologue: saved `rbp`
(holding `rbp₀`), padding, the spilled argument (holding `arg`), the unused 8
bytes. -/
abbrev Own (r rbp₀ : BitVec 64) (arg : Int) (X : Mem 64 → Prop) : Mem 64 → Prop :=
  Int.toBytes 8 rbp₀.toInt =@ (r - 8) ⋆ (3 ?@ (r - 12)
    ⋆ (Int.toBytes 4 arg =@ (r - 16) ⋆ (8 ?@ (r - 24) ⋆ X)))

/-- `CallPre`'s memory as the entry block reads it. -/
theorem CallPre.cells {n : Nat} {R : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (hn : n < 2 ^ 32) (h : CallPre (need n) R ra t) :
    t.dmem =⋆ RetCell ra (t.regs.get64 .rsp)
      ⋆ OwnCells (t.regs.get64 .rsp) (Reserve (below n) (t.regs.get64 .rsp - 24) ⋆ R) := by
  have hmem : t.dmem =⋆ RetCell ra (t.regs.get64 .rsp)
      ⋆ (Reserve (need n) (t.regs.get64 .rsp) ⋆ R) := h
  rw [Reserve_cells _ _ _ (need_le hn)] at hmem
  exact hmem

/-- `CallPost` as the exit block leaves it: the own bytes as the cells the code
used, the rest of the reservation below them. The blocks establish this;
`CallPost.of_cells` folds it (`hpost` of `ProcSpec.of_cfg_post`). -/
abbrev CallPostCells (n : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t.regs.get64 .rbp ∧ SavedRegs t s
  ∧ (s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp)
      ⋆ OwnCells (t.regs.get64 .rsp) (Reserve (below n) (t.regs.get64 .rsp - 24) ⋆ R))

theorem CallPost.of_cells {n : Nat} {R : Mem 64 → Prop} {ra : Int64} {t s : MachineData}
    (hn : n < 2 ^ 32) (h : CallPostCells n R ra t s) : CallPost (need n) R ra t s := by
  obtain ⟨h₁, h₂, h₃, hmem⟩ := h
  exact ⟨h₁, h₂, h₃, by rw [Reserve_cells _ _ _ (need_le hn)]; exact hmem⟩

/-! ## The specifications -/

/-- `even` at `n`: the convention with `need n` bytes of stack, the argument
in `edi`. -/
abbrev EvenPre (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (need n) R ra t ∧ ArgU32 t n

/-- `even` at `n` returns: the convention, and `al = (n + 1) % 2`. -/
abbrev EvenPost (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (need n) R ra t s ∧ RetU8 s ((n + 1) % 2)

/-- `odd` at `n`: as `even`. -/
abbrev OddPre (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (need n) R ra t ∧ ArgU32 t n

/-- `odd` at `n` returns: the convention, and `al = n % 2`. -/
abbrev OddPost (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (need n) R ra t s ∧ RetU8 s (n % 2)

/-- The spec of `even` at `n`: a `ProcSpec` whose logical variable is the
caller's memory `R`. -/
abbrev EvenSpec [CodeEnv] (n : Nat) : Prop :=
  cenv.ProcSpec ((_root_.Executable.labels cenv).label "even") (EvenPre n) (EvenPost n)

abbrev OddSpec [CodeEnv] (n : Nat) : Prop :=
  cenv.ProcSpec ((_root_.Executable.labels cenv).label "odd") (OddPre n) (OddPost n)

/-- What a file assumes of its partner: its spec at every smaller argument. -/
abbrev EvenSpecBelow [CodeEnv] (n : Nat) : Prop := ∀ m < n, EvenSpec m

abbrev OddSpecBelow [CodeEnv] (n : Nat) : Prop := ∀ m < n, OddSpec m

/-- The argument fits its register. -/
theorem ArgU32.lt {t : MachineData} {n : Nat} (h : ArgU32 t n) : n < 2 ^ 32 :=
  h ▸ Nat.mod_lt _ (by decide)

end Kraken.Examples.EvenOddGhost
