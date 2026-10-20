/-
AArch64 counterpart of x64's `Kraken/X64/Examples/EvenOddGhost/` (`Spec`,
`Even`, `Odd`, `Link` in one file): the mutually recursive

```c
bool odd(unsigned long n);
bool even(unsigned long n) { if (!n) return true;  return odd(n-1); }
bool odd(unsigned long n)  { if (!n) return false; return even(n-1); }
```

written by hand in AArch64 assembly, each proved against the other's
specification at smaller arguments (`even_spec`, `odd_spec`), tied by strong
induction (`even_odd_spec`). The specifications are in the ghost style: the
caller's memory `R` is the logical variable of the `ProcSpec`, fixed at the
call site with `call_proc_spec_at`.

## The calling convention (AAPCS64, as these bodies rely on it)

* the return address is in `X30` on entry (`t.lr = ra`); `BL` writes it, so a
  procedure that calls another saves `X30` first: the frame record
  `STP X29, X30, [SP, #-16]!` … `LDP X29, X30, [SP], #16`;
* `SP` is 16-byte aligned (`Aligned`), as every `SP`-based access requires;
* the argument and the result are in `X0`;
* on return `SP` and `X29` (the frame pointer) hold their entry values, and so
  do the callee-saved `X19`–`X28` (`SavedRegs`);
* the `d` bytes below the entry `SP` are the procedure's to use: the caller
  reserves them (`Reserve d sp`, as x64's `Kraken.SysV.Reserve`) and gets them
  back.

Unlike x64, the return address is not on the stack: `CallPre` has no
`RetCell`, and a call needs no stack slot of its own. Each level of recursion
uses one 16-byte frame record, so the pair needs `need n = 16 (n + 1)` bytes at
argument `n`.

## Semantics

`even` returns `(n + 1) % 2`, `odd` returns `n % 2`, in `X0`.
-/
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Cfg
import Kraken.AArch64.WP.RulesCF
import Kraken.AArch64.WP.Rules
import Kraken.SepCells

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order
open Mem
open Std.ExtHashMap

set_option mvcgen.warning false
set_option experimental.vcgen true
set_option grind.warning false

namespace Kraken.AArch64.Examples.WPEvenOdd

/-! ## The convention -/

/-- `d` bytes of free stack just below `r` (x64's `Kraken.SysV.Reserve`). A
`def`, so that `grind` moves it as one cell. -/
def Reserve (d : Nat) (r : BitVec 64) : Mem 64 → Prop := d ?@ (r - .ofNat 64 d)

/-- The reservation with `a` bytes carved off its top (x64's
`Kraken.SysV.Reserve_split`). -/
theorem Reserve_split (a d : Nat) (r : BitVec 64) (h : a + d ≤ 2 ^ 64) :
    Reserve (a + d) r = a ?@ (r - .ofNat 64 a) ⋆ Reserve d (r - .ofNat 64 a) := by
  unfold Reserve
  rw [Block.split_at (r - BitVec.ofNat 64 (a + d)) (a + d) d (by omega) h, sep_comm]
  have e1 : r - BitVec.ofNat 64 (a + d) + BitVec.ofNat 64 d = r - BitVec.ofNat 64 a := by
    bv_omega
  have e2 : r - BitVec.ofNat 64 a - BitVec.ofNat 64 d = r - BitVec.ofNat 64 (a + d) := by
    bv_omega
  rw [e1, e2, Nat.add_sub_cancel]

/-- `SP` is 16-byte aligned. -/
abbrev Aligned (t : MachineData) : Prop := t.regs.SP.toBitVec % 16#64 = 0#64

/-- The callee-saved registers other than `X29`. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.X19 = t.regs.X19 ∧ s.regs.X20 = t.regs.X20 ∧ s.regs.X21 = t.regs.X21
  ∧ s.regs.X22 = t.regs.X22 ∧ s.regs.X23 = t.regs.X23 ∧ s.regs.X24 = t.regs.X24
  ∧ s.regs.X25 = t.regs.X25 ∧ s.regs.X26 = t.regs.X26 ∧ s.regs.X27 = t.regs.X27
  ∧ s.regs.X28 = t.regs.X28

/-- The convention's share of a precondition, with caller's memory `R`: the
return address in `X30`, `SP` aligned, `d` bytes reserved below it. -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  t.lr = ra ∧ Aligned t ∧ d ≤ 2 ^ 64 ∧ (t.dmem =⋆ Reserve d t.regs.SP.toBitVec ⋆ R)

/-- The convention's share of a postcondition: `SP`, `X29` and the callee-saved
registers as they were, the reservation given back. -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.SP = t.regs.SP ∧ s.regs.X29 = t.regs.X29 ∧ SavedRegs t s
  ∧ (s.dmem =⋆ Reserve d t.regs.SP.toBitVec ⋆ R)

/-! ## The specifications -/

/-- The stack the pair uses at argument `n`: one 16-byte frame record per
level. -/
abbrev need (n : Nat) : Nat := 16 * (n + 1)

abbrev EvenPre (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (need n) R ra t ∧ t.regs.X0.toNat = n

abbrev EvenPost (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (need n) R ra t s ∧ s.regs.X0.toNat = (n + 1) % 2

abbrev OddPre (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (need n) R ra t ∧ t.regs.X0.toNat = n

abbrev OddPost (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (need n) R ra t s ∧ s.regs.X0.toNat = n % 2

abbrev EvenSpec [CodeEnv] (n : Nat) : Prop :=
  cenv.ProcSpec ((_root_.Executable.labels cenv).label "even") (EvenPre n) (EvenPost n)

abbrev OddSpec [CodeEnv] (n : Nat) : Prop :=
  cenv.ProcSpec ((_root_.Executable.labels cenv).label "odd") (OddPre n) (OddPost n)

/-! ## The bodies -/

def even_body : Program := parseAArch64("
even:
  cbnz x0, .Leven_rec
  movz x0, #1
  ret
.Leven_rec:
  stp x29, x30, [sp, #-16]!
  sub x0, x0, #1
  bl odd
  ldp x29, x30, [sp], #16
  ret
")

def odd_body : Program := parseAArch64("
odd:
  cbnz x0, .Lodd_rec
  movz x0, #0
  ret
.Lodd_rec:
  stp x29, x30, [sp, #-16]!
  sub x0, x0, #1
  bl even
  ldp x29, x30, [sp], #16
  ret
")

/-! ## The frame

The frame record sits at `sp - 16`, which the `STP` computes as
`sp + (-16 : Int64).toBitVec`; the cells are stated at that term (and at it
plus 8), so that `grind` matches each access against its cell's base
exactly (see the note on addresses in `SepCells`). -/

/-- The frame offset as a bit vector. -/
theorem neg16_toBitVec : (-16 : Int64).toBitVec = -16#64 := rfl

/-- Where the frame record goes. -/
abbrev fr (sp : BitVec 64) : BitVec 64 := sp + (-16 : Int64).toBitVec

/-- The reservation as the code uses it: the two 8-byte slots of the frame
record, and the callee's reservation below them. Used at the entry (`hpre`)
and the exit (`hpost`), not inside `grind`. -/
theorem Reserve_cells (n : Nat) (r : BitVec 64) (X : Mem 64 → Prop) (hn : need n ≤ 2 ^ 64) :
    Reserve (need n) r ⋆ X
      = 8 ?@ fr r ⋆ (8 ?@ (fr r + 8#64) ⋆ (Reserve (16 * n) (fr r) ⋆ X)) := by
  have e : need n = 16 + 16 * n := by unfold need; omega
  have efr : r - BitVec.ofNat 64 16 = fr r := by
    simp only [fr]; rw [neg16_toBitVec]; bv_omega
  rw [e, Reserve_split 16 (16 * n) r (by omega), efr,
    show (16 : Nat) = 8 + 8 from rfl, Block.split _ 8 8 (by decide)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The bytes of a register read back from its 8-byte cell. -/
@[grind =] theorem ofInt_ofBytes_toBytes_64 (v : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl v

/-- The frame record leaves `SP` aligned. -/
@[grind →] theorem aligned_fr {sp : BitVec 64} (h : sp % 16#64 = 0#64) : fr sp % 16#64 = 0#64 := by
  have h' : sp.toNat % 16 = 0 := by simpa using congrArg BitVec.toNat h
  simp only [fr]; rw [neg16_toBitVec]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_add,
    show (-16#64 : BitVec 64).toNat = 18446744073709551600 from rfl,
    show (16#64 : BitVec 64).toNat = 16 from rfl, show (0#64 : BitVec 64).toNat = 0 from rfl,
    Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
  omega

/-- The caller's memory of a recursive call: the saved frame record over `R`. -/
abbrev Frame (t₀ : MachineData) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  Int.toBytes 8 t₀.regs.X29.toBitVec.toInt =@ fr t₀.regs.SP.toBitVec
    ⋆ (Int.toBytes 8 t₀.regs.X30.toBitVec.toInt =@ (fr t₀.regs.SP.toBitVec + 8#64) ⋆ R)

/-- The table entry shared by both blocks of either procedure: the entry
state, with its memory as the code uses it. -/
abbrev Entry (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Prop :=
  t₀.lr = ra ∧ Aligned t₀ ∧ need n ≤ 2 ^ 64 ∧ t₀.regs.X0.toNat = n
  ∧ (t₀.dmem =⋆ 8 ?@ fr t₀.regs.SP.toBitVec ⋆ (8 ?@ (fr t₀.regs.SP.toBitVec + 8#64)
      ⋆ (Reserve (16 * n) (fr t₀.regs.SP.toBitVec) ⋆ R)))

/-- `CallPost` as the exit leaves it: the frame record's slots as cells. -/
abbrev PostCells (n : Nat) (R : Mem 64 → Prop) (t₀ s : MachineData) : Prop :=
  s.regs.SP = t₀.regs.SP ∧ s.regs.X29 = t₀.regs.X29 ∧ SavedRegs t₀ s ∧ need n ≤ 2 ^ 64
  ∧ (s.dmem =⋆ 8 ?@ fr t₀.regs.SP.toBitVec ⋆ (8 ?@ (fr t₀.regs.SP.toBitVec + 8#64)
      ⋆ (Reserve (16 * n) (fr t₀.regs.SP.toBitVec) ⋆ R)))

/-- Normalise the register file after the frame record and the call: reads of
registers through `setXReg`/`setRegOrSp`/`setRegOrZr`, the `SP` writeback of
the pre- and post-indexed addressing, and the decidable register comparisons. Run
before `grind_cells`, so that `grind` sees register values, not register-file
terms. -/
local macro "regs_simp" : tactic => `(tactic| simp only [
    Reg64s.getRegOrSp_X, Reg64s.setRegOrSp_X, Reg64s.getRegOrZr_X, Reg64s.setRegOrZr_X,
    Reg64s.SP_setXReg, Reg64s.getRegOrSp_SP, Reg64s.setRegOrSp_SP, AddrExpr.eval_pre,
    AddrExpr.eval_post, AddrExpr.SPAligned_SP, ConstExpr.interp_int64, MachineData.regs_setLr,
    MachineData.dmem_setLr, MachineData.status_setLr, Reg64s.X0_setXReg, Reg64s.X1_setXReg,
    Reg64s.X2_setXReg, Reg64s.X3_setXReg, Reg64s.X4_setXReg, Reg64s.X5_setXReg,
    Reg64s.X6_setXReg, Reg64s.X7_setXReg, Reg64s.X8_setXReg, Reg64s.X9_setXReg,
    Reg64s.X10_setXReg, Reg64s.X11_setXReg, Reg64s.X12_setXReg, Reg64s.X13_setXReg,
    Reg64s.X14_setXReg, Reg64s.X15_setXReg, Reg64s.X16_setXReg, Reg64s.X17_setXReg,
    Reg64s.X18_setXReg, Reg64s.X19_setXReg, Reg64s.X20_setXReg, Reg64s.X21_setXReg,
    Reg64s.X22_setXReg, Reg64s.X23_setXReg, Reg64s.X24_setXReg, Reg64s.X25_setXReg,
    Reg64s.X26_setXReg, Reg64s.X27_setXReg, Reg64s.X28_setXReg, Reg64s.X29_setXReg,
    Reg64s.X30_setXReg, Reg64s.getXReg_X0, Reg64s.getXReg_X1, Reg64s.getXReg_X2,
    Reg64s.getXReg_X3, Reg64s.getXReg_X4, Reg64s.getXReg_X5, Reg64s.getXReg_X6,
    Reg64s.getXReg_X7, Reg64s.getXReg_X8, Reg64s.getXReg_X9, Reg64s.getXReg_X10,
    Reg64s.getXReg_X11, Reg64s.getXReg_X12, Reg64s.getXReg_X13, Reg64s.getXReg_X14,
    Reg64s.getXReg_X15, Reg64s.getXReg_X16, Reg64s.getXReg_X17, Reg64s.getXReg_X18,
    Reg64s.getXReg_X19, Reg64s.getXReg_X20, Reg64s.getXReg_X21, Reg64s.getXReg_X22,
    Reg64s.getXReg_X23, Reg64s.getXReg_X24, Reg64s.getXReg_X25, Reg64s.getXReg_X26,
    Reg64s.getXReg_X27, Reg64s.getXReg_X28, Reg64s.getXReg_X29, Reg64s.getXReg_X30, ↓reduceIte,
    reduceCtorEq] at *)

variable [CodeEnv]

/-! ## `even` -/

abbrev even_table (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "even", s => s = t₀ ∧ Entry n R ra t₀
  | ".Leven_rec", s => s = t₀ ∧ n ≠ 0 ∧ Entry n R ra t₀
  | _, _ => False

theorem even_spec (hpl : Program.PlacedIn even_body) (n : Nat) (ih : ∀ m < n, OddSpec m) :
    EvenSpec n := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := even_body) (even_table n)
    (fun R _ t₀ s => PostCells n R t₀ s ∧ s.regs.X0.toNat = (n + 1) % 2)
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [even_body]
    · vcgen
      all_goals grind_cells
    · rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.2.1
      · vcgen [MachineWP.call_proc_spec_at (Frame t₀ R) "odd" (ih k (Nat.lt_succ_self k))]
        all_goals call_simp
        all_goals try refine ⟨?_, fun s' hpost => ?_⟩
        all_goals try (vcgen; all_goals call_simp)
        all_goals regs_simp
        -- the exit: the return through `X30`, then each conjunct of the
        -- postcondition on its own (`grind` on the whole conjunction is slow)
        all_goals first
          | (refine Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> grind_cells)
          | grind_cells
  · rintro R ra t ⟨⟨hra, hal, hn, hmem⟩, harg⟩
    exact ⟨rfl, hra, hal, hn, harg, by rw [← Reserve_cells n _ R hn]; exact hmem⟩
  · rintro R ra t₀ s ⟨⟨h1, h2, h3, hn, hmem⟩, hres⟩
    exact ⟨⟨h1, h2, h3, by rw [Reserve_cells n _ R hn]; exact hmem⟩, hres⟩

/-! ## `odd` -/

abbrev odd_table (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "odd", s => s = t₀ ∧ Entry n R ra t₀
  | ".Lodd_rec", s => s = t₀ ∧ n ≠ 0 ∧ Entry n R ra t₀
  | _, _ => False

theorem odd_spec (hpl : Program.PlacedIn odd_body) (n : Nat) (ih : ∀ m < n, EvenSpec m) :
    OddSpec n := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := odd_body) (odd_table n)
    (fun R _ t₀ s => PostCells n R t₀ s ∧ s.regs.X0.toNat = n % 2)
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [odd_body]
    · vcgen
      all_goals grind_cells
    · rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.2.1
      · vcgen [MachineWP.call_proc_spec_at (Frame t₀ R) "even" (ih k (Nat.lt_succ_self k))]
        all_goals call_simp
        all_goals try refine ⟨?_, fun s' hpost => ?_⟩
        all_goals try (vcgen; all_goals call_simp)
        all_goals regs_simp
        -- the exit: the return through `X30`, then each conjunct of the
        -- postcondition on its own (`grind` on the whole conjunction is slow)
        all_goals first
          | (refine Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> grind_cells)
          | grind_cells
  · rintro R ra t ⟨⟨hra, hal, hn, hmem⟩, harg⟩
    exact ⟨rfl, hra, hal, hn, harg, by rw [← Reserve_cells n _ R hn]; exact hmem⟩
  · rintro R ra t₀ s ⟨⟨h1, h2, h3, hn, hmem⟩, hres⟩
    exact ⟨⟨h1, h2, h3, by rw [Reserve_cells n _ R hn]; exact hmem⟩, hres⟩

/-! ## Tying the two proofs

Strong induction on `n` discharges both assumptions at once (x64's
`EvenOddGhost/Link.lean`). What remains assumed is the placement of both
bodies in the ambient code: each `BL` reaches its target through the target's
`ProcSpec`, stated at the target's address. -/

/-- Both specifications, at every argument. -/
theorem even_odd_spec (hpe : Program.PlacedIn even_body)
    (hpo : Program.PlacedIn odd_body) (n : Nat) : EvenSpec n ∧ OddSpec n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    exact ⟨even_spec hpe n (fun m hm => (ih m hm).2),
      odd_spec hpo n (fun m hm => (ih m hm).1)⟩

theorem even_spec_all (hpe : Program.PlacedIn even_body)
    (hpo : Program.PlacedIn odd_body) (n : Nat) : EvenSpec n := (even_odd_spec hpe hpo n).1

theorem odd_spec_all (hpe : Program.PlacedIn even_body)
    (hpo : Program.PlacedIn odd_body) (n : Nat) : OddSpec n := (even_odd_spec hpe hpo n).2

end Kraken.AArch64.Examples.WPEvenOdd
