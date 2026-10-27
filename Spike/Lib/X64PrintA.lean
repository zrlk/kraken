/-
**`scc_rt_print` against a source that prints byte by byte** (x64): the
function of `Spike/Lib/X64Print.lean` (same blocks, same graph) with
invariants that track how far the output has got, for a source whose
`print` is an emit loop: the x64 twin of `Spike/Lib/A64PrintA.lean`.

Ghost parameters: the caller's `%rbp`, the return address `ra`, the buffer's
address `buf0` and length `len0` at entry, and two predicates on the source
control: `P k` (the source has printed the first `k` bytes and is ready
for byte `k`) and `Q k` (after `k` bytes, a refused write justifies the
abort). Inside the loop the frame's cells hold `buf0 + k` (at `-8`) and
`len0 - k` (at `-16`) for some `k ≤ len0` with `P k` (`JL`, `JI`).

The `write` system call is a given node (`hsys`). From the loop's state
with `k < len0`, `%rdi = 1`, `%rax = 1`, `%rsi = buf0 + k`,
`%rdx = len0 - k`, it returns to the next instruction with the frame's cells
kept and a result `r` in `%rax`, which `RC0` classifies (as on AArch64):

- `-EINTR`/`-EAGAIN`: the source has not moved (`P k`);
- `0 < r ≤ len0 - k`: the source has printed `r` more bytes (`P (k + r)`);
- a refusal (`writeRefused`): `Q k`.

Every block node keeps the source where it is: only the system call moves
it. The specification:

- **entry** (`.e`): `P 0`, `%rdi = buf0`, `%rsi = len0`, `%rbp = rbp0`, `ra`
  in its cell;
- **return** (`.ret`): pc at `ra`, `%rbp` restored, `P len0`;
- **abort** (`.abort`): pc at `scc_rt_abort`, `%rdi = 4`, `Q k` for some `k`.

`len0 < 2^63`: a positive count is then a positive signed number, so the
code's `jle` separates it from a refusal.
-/
import Spike.Lib.X64Print
import Scc.Cert.Rt.X64Print

set_option linter.unusedSimpArgs false

namespace Spike.Lib.X64.PrintA

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64
open Spike.Lib.X64.Print (PN PX x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI oE pcSys
  x0_ok x1_ok x2_ok x3_ok x4_ok x5_ok x6_ok x7_ok x8_ok x9_ok x10_ok x11_ok x12_ok x13_ok
  x0_run x1_run x2_run x3_run x4_run x5_run x6_run x7_run x8_run x9_run x10_run x11_run x12_run x13_run)
open Scc.Sem.Kernel (writeRefused neg eintr eagain)

/-! ## Flags and arithmetic

The ISA-independent ones are `Spike.Lib.A64.PrintA`'s, restated: the two
ISAs' syntax modules cannot be imported together. -/

/-- `-4` (`-EINTR`), as the code builds it. -/
abbrev C4 : BitVec 64 := 18446744073709551612#64
/-- `-11` (`-EAGAIN`), as the code builds it. -/
abbrev C11 : BitVec 64 := 18446744073709551605#64

theorem c4_eq : C4 = neg eintr := by decide
theorem c11_eq : C11 = neg eagain := by decide

/-- A count below `2^63` is no refusal and not negative. -/
theorem pos_not_le {r : BitVec 64} (h0 : 0 < r.toNat) (h : r.toNat < 2 ^ 63) : ¬(r = 0#64 ∨ r.msb = true) := by
  rintro (rfl | hm)
  · simp at h0
  · rw [BitVec.msb_eq_decide] at hm; simp at hm; omega

/-- A refusal is zero or negative. -/
theorem refused_le {r : BitVec 64} (h : writeRefused r = true) : r = 0#64 ∨ r.msb = true := by
  simp only [writeRefused, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨h, -⟩, -⟩
  · exact .inl h
  · right; rw [BitVec.msb_eq_decide]; simp only [Scc.Sem.Kernel.maxErrno] at h; simp; omega

theorem refused_ne4 {r : BitVec 64} (h : writeRefused r = true) : r ≠ C4 := by
  rintro rfl; revert h; decide

theorem refused_ne11 {r : BitVec 64} (h : writeRefused r = true) : r ≠ C11 := by
  rintro rfl; revert h; decide

theorem small_ne {r c : BitVec 64} (h : r.toNat < 2 ^ 63) (hc : 2 ^ 63 ≤ c.toNat) : r ≠ c := by
  rintro rfl; omega

/-- The cursor's advance. -/
theorem adv_buf (b : BitVec 64) (k : Nat) (r : BitVec 64) :
    b + BitVec.ofNat 64 k + r = b + BitVec.ofNat 64 (k + r.toNat) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- The remaining length's decrease. -/
theorem adv_len {len k : Nat} {r : BitVec 64} (hl : len < 2 ^ 64) (hr : r.toNat ≤ len - k) :
    BitVec.ofNat 64 (len - k) - r = BitVec.ofNat 64 (len - (k + r.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : len - k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : len - (k + r.toNat) < 2 ^ 64)]
  have := r.isLt
  omega

theorem len_zero {len k : Nat} (hl : len < 2 ^ 64) (hk : k ≤ len) :
    BitVec.ofNat 64 (len - k) = 0#64 ↔ k = len := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro h; subst h; simp

/-- `cmpq; je`: the difference is zero iff the operands are equal. -/
theorem sub_z {a b : BitVec 64} : a - b = 0#64 ↔ a = b := by
  constructor <;> intro h
  · bv_omega
  · subst h; simp

/-! ## The specification -/

section Spec

variable (lab : Label → Int64) (rbp0 ra buf0 : BitVec 64) (len0 : Nat) (P Q : Nat → Ctl → Prop)

/-- The frame's cells after `k` bytes: the caller's `%rbp`, the return
address, the cursor and the remaining length. -/
def JL (k : Nat) (σ : AS) : Prop :=
  σ.slot 0 = rbp0 ∧ σ.slot 8 = ra ∧ σ.slot (-8) = buf0 + BitVec.ofNat 64 k ∧
    σ.slot (-16) = BitVec.ofNat 64 (len0 - k) ∧ k ≤ len0

/-- The loop's invariant: `k` bytes out, the source ready for byte `k`. -/
def JI (σ : AS) (c : Ctl) : Prop := ∃ k, JL rbp0 ra buf0 len0 k σ ∧ P k c

/-- The loop's invariant with bytes left. -/
def JIlt (σ : AS) (c : Ctl) : Prop := ∃ k, JL rbp0 ra buf0 len0 k σ ∧ k < len0 ∧ P k c

/-- A positive count `r`: `r` more bytes out. -/
def RC2 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop :=
  (0 < r.toNat ∧ r.toNat ≤ len0 - k ∧ P (k + r.toNat) c) ∨ (writeRefused r = true ∧ Q k c)

/-- The result past the `-EINTR` check. -/
def RC1 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop := (r = C11 ∧ P k c) ∨ RC2 len0 P Q k r c

/-- **What the system call returns**: `-EINTR`/`-EAGAIN` with the source
unmoved, a positive count with the source `r` bytes further, or a refusal
justifying the abort. -/
def RC0 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop := (r = C4 ∧ P k c) ∨ RC1 len0 P Q k r c

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_print", oE, fun σ c => P 0 c ∧ σ.regs.rbp.toBitVec = rbp0 ∧ σ.slot 8 = ra ∧
      σ.regs.get64 .rdi = buf0 ∧ σ.regs.get64 .rsi = BitVec.ofNat 64 len0⟩
  | .n1 => ⟨lab ".Lscc_rt_print.entry", oI, JI rbp0 ra buf0 len0 P⟩
  | .loop => ⟨lab ".Lscc_rt_print.loop", oI, JI rbp0 ra buf0 len0 P⟩
  | .n3 => ⟨lab ".Lscc_rt_print.loop" + 20, oI, JIlt rbp0 ra buf0 len0 P⟩
  | .write => ⟨lab ".Lscc_rt_print.write", oI, JIlt rbp0 ra buf0 len0 P⟩
  | .sys => ⟨pcSys lab, oI, fun σ c => JIlt rbp0 ra buf0 len0 P σ c ∧ σ.regs.get64 .rdi = 1 ∧
      σ.regs.get64 .rax = 1 ∧ σ.regs.get64 .rsi = σ.slot (-8) ∧ σ.regs.get64 .rdx = σ.slot (-16)⟩
  | .n5 => ⟨lab ".Lscc_rt_print.write" + 22, oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ RC0 len0 P Q k (σ.regs.get64 .rax) c⟩
  | .n6 => ⟨lab ".Lscc_rt_print.write" + 42, oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-24)) c⟩
  | .chk2 => ⟨lab ".Lscc_rt_print.chk2", oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-24)) c⟩
  | .n8 => ⟨lab ".Lscc_rt_print.chk2" + 16, oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-24)) c⟩
  | .chk3 => ⟨lab ".Lscc_rt_print.chk3", oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-24)) c⟩
  | .n10 => ⟨lab ".Lscc_rt_print.chk3" + 16, oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ 0 < (σ.slot (-24)).toNat ∧ (σ.slot (-24)).toNat ≤ len0 - k ∧
        P (k + (σ.slot (-24)).toNat) c⟩
  | .adv => ⟨lab ".Lscc_rt_print.adv", oI, fun σ c =>
      ∃ k, JL rbp0 ra buf0 len0 k σ ∧ 0 < (σ.slot (-24)).toNat ∧ (σ.slot (-24)).toNat ≤ len0 - k ∧
        P (k + (σ.slot (-24)).toNat) c⟩
  | .fail => ⟨lab ".Lscc_rt_print.fail", oI, fun _ c => ∃ k, Q k c⟩
  | .done => ⟨lab ".Lscc_rt_print.done", oI, fun σ c => σ.slot 0 = rbp0 ∧ σ.slot 8 = ra ∧ P len0 c⟩

/-- **The exits**: the return to `ra` with `%rbp` restored and all `len0`
bytes out, and the abort with code 4 after a refusal. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => σ.regs.get64 .rbp = rbp0 ∧ P len0 c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-40, []⟩, fun σ c => σ.regs.get64 .rdi = 4 ∧ ∃ k, Q k c⟩

/-- **The function's states inside `W`**, none moved by `K`: one obligation
per block node (the system call is a given node). -/
structure PrintAW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .e) x0
  n1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n1) x1
  loop : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .loop) x2
  n3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n3) x3
  write : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .write) x4
  n5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5) x5
  n6 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n6) x6
  chk2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .chk2) x7
  n8 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n8) x8
  chk3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .chk3) x9
  n10 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n10) x10
  adv : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .adv) x11
  fail : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .fail) x12
  done : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .done) x13

/-- The function is inside the trivial predicate, with no outside moves. -/
theorem PrintAW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    PrintAW rbp0 ra buf0 len0 P Q (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv⟩

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {c0 : Ctl} {rbp0 ra buf0 : BitVec 64} {len0 : Nat}
  {P Q : Nat → Ctl → Prop}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code, its `W` obligation; the
source stays; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) hW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- Hitting node `j`: the pc and offsets; the invariant is left, unfolded. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> try simp only [N]) <;>
    try first | rfl | exact hentry | (simp only [Int64.add_assoc]; rfl))

/-- Hitting exit `x`: the offsets; the pc and the invariant are left. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> try simp only [E]) <;> try rfl)

set_option maxHeartbeats 1000000 in
/-- **`scc_rt_print` is one segment inside `W`** from its entry to its
return or its abort, against a source that prints byte by byte: the block
nodes keep the source where it is, and the system call (`hsys`, a given
segment inside `W`) moves it by the count it returns. The code is
`seg_printW`'s (`Print.Code`, any `c0`). -/
theorem seg_printAW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hcode : Print.Code c0 rbp0 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hW : PrintAW rbp0 ra buf0 len0 P Q W K exe endPc R F)
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label rbp0 ra len0 P Q x) s c) := by
  have hl64 : len0 < 2 ^ 64 := by omega
  refine fn_segW (N := N _ rbp0 ra buf0 len0 P Q) (E := E _ rbp0 ra len0 P Q) (fun i => ?_) PN.e
  cases i
  case sys => exact seg_givenW PN.n5 hsys
  case e =>
    node x0 x0_ok e; rw [N, x0_run]; hit PN.n1
    obtain ⟨hP, hbp, h8, h0, h1⟩ := hJ
    exact ⟨0, ⟨by simp [Spike.Lib.upd_apply, hbp], by simp [Spike.Lib.upd_apply, h8],
      by simp [Spike.Lib.upd_apply]; exact h0, by simp [Spike.Lib.upd_apply]; exact h1, Nat.zero_le _⟩, hP⟩
  case n1 => node x1 x1_ok n1; rw [N, x1_run]; hit PN.loop; exact hJ
  case loop =>
    node x2 x2_ok loop; rw [N, x2_run]
    obtain ⟨k, ⟨h0, h8, h16, h24, hk⟩, hP⟩ := hJ
    rw [h24]
    by_cases hz : k = len0
    · subst hz
      simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, ite_true]
      hit PN.done
      exact ⟨h0, h8, hP⟩
    · have hz' : ¬ BitVec.ofNat 64 (len0 - k) = 0#64 := fun h => hz ((len_zero hl64 hk).1 h)
      simp only [hz', ite_false]
      hit PN.n3
      exact ⟨k, ⟨h0, h8, h16, h24, hk⟩, by omega, hP⟩
  case n3 => node x3 x3_ok n3; rw [N, x3_run]; hit PN.write; exact hJ
  case write =>
    node x4 x4_ok write; rw [N, x4_run]; hit PN.sys
    refine ⟨hJ, ?_⟩
    simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne]
  case n5 =>
    node x5 x5_ok n5; rw [N, x5_run]
    obtain ⟨k, hL, hr⟩ := hJ
    have hL' : JL rbp0 ra buf0 len0 k { σ with slot := Spike.Lib.upd σ.slot (-24) σ.regs.rax.toBitVec } := by
      obtain ⟨h0, h8, h16, h24, hk⟩ := hL
      exact ⟨by simp [Spike.Lib.upd_apply, h0], by simp [Spike.Lib.upd_apply, h8],
        by simp [Spike.Lib.upd_apply, h16], by simp [Spike.Lib.upd_apply, h24], hk⟩
    split
    · rename_i hz
      have hz := sub_z.1 hz
      hit PN.loop
      refine ⟨k, hL', ?_⟩
      have hr : RC0 len0 P Q k σ.regs.rax.toBitVec c := hr
      rcases hr with ⟨-, hP⟩ | ⟨h11, -⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at h11; exact absurd h11 (by decide)
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C4, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne4 hw)
    · rename_i hz
      hit PN.n6
      refine ⟨k, hL', ?_⟩
      have hr : RC0 len0 P Q k σ.regs.rax.toBitVec c := hr
      rcases hr with ⟨h4, -⟩ | h
      · exact absurd (sub_z.2 h4) hz
      · simpa [Spike.Lib.upd_apply] using h
  case n6 => node x6 x6_ok n6; rw [N, x6_run]; hit PN.chk2; exact hJ
  case chk2 =>
    node x7 x7_ok chk2; rw [N, x7_run]
    obtain ⟨k, hL, hr⟩ := hJ
    split
    · rename_i hz
      have hz := sub_z.1 hz
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C11, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne11 hw)
    · rename_i hz
      hit PN.n8
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h11, -⟩ | h
      · exact absurd (sub_z.2 h11) hz
      · exact h
  case n8 => node x8 x8_ok n8; rw [N, x8_run]; hit PN.chk3; exact hJ
  case chk3 =>
    node x9 x9_ok chk3; rw [N, x9_run]
    obtain ⟨k, hL, hr⟩ := hJ
    split
    · rename_i hy
      rcases hr with ⟨h0, hle, -⟩ | ⟨-, hQ⟩
      · exact absurd hy.symm (pos_not_le h0 (by omega))
      · hit PN.fail
        exact ⟨k, hQ⟩
    · rename_i hn
      rcases hr with ⟨h0, hle, hP⟩ | ⟨hw, -⟩
      · hit PN.n10
        exact ⟨k, hL, h0, hle, hP⟩
      · exact absurd (refused_le hw).symm hn
  case n10 => node x10 x10_ok n10; rw [N, x10_run]; hit PN.adv; exact hJ
  case adv =>
    node x11 x11_ok adv; rw [N, x11_run]; hit PN.loop
    obtain ⟨k, ⟨h0, h8, h16, h24, hk⟩, hr0, hle, hP⟩ := hJ
    refine ⟨k + (σ.slot (-24)).toNat, ⟨?_, ?_, ?_, ?_, by omega⟩, hP⟩
    · simp [Spike.Lib.upd_apply, h0]
    · simp [Spike.Lib.upd_apply, h8]
    · simp only [Spike.Lib.upd_apply]; simp only [show (-8 : Int) ≠ -16 by decide, ite_true, ite_false]
      rw [h16, BitVec.add_comm, adv_buf]
    · simp only [Spike.Lib.upd_apply, ite_true]; rw [h24, adv_len hl64 hle]
  case fail =>
    node x12 x12_ok fail; rw [N, x12_run]; exit PX.abort
    exact ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne], hJ⟩
  case done =>
    node x13 x13_ok done; rw [N, x13_run]; exit PX.ret
    · rw [hJ.2.1]
    · exact ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, hJ.1], hJ.2.2⟩

/-- **`scc_rt_print` is one segment inside `W`** against a byte-by-byte
source in any valid layout `exe` of cells `cells` with `printIn cells = true`
(`hello1_print` for `hello1Cells`), given its write system call (`hsys`). -/
theorem seg_printA_ofW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop}
    [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Scc.Cert.Rt.X64.Lays exe cells kp) (hend : endPc = Scc.Cert.Rt.X64.endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hW : PrintAW rbp0 ra buf0 len0 P Q W K exe endPc R F)
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label rbp0 ra len0 P Q x) s c) := by
  simp only [Scc.Cert.Rt.X64.Print.printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, hgap⟩ := hprog
  refine seg_printAW (c0 := ⟨.ret .unit, [], none⟩) hF hR hlo hhi hlen
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [Scc.Cert.Rt.X64.label_labelGapB hp hgap]; rfl) hW hsys
  · exact Scc.Cert.Rt.X64.code_field hp hend h0 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h1 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h2 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h3 rfl
  · exact Scc.Cert.Rt.X64.code_field hp hend h4 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h5 rfl
  · exact Scc.Cert.Rt.X64.code_field hp hend h6 rfl
  · exact Scc.Cert.Rt.X64.code_field hp hend h7 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h8 rfl
  · exact Scc.Cert.Rt.X64.code_field hp hend h9 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h10 rfl
  · exact Scc.Cert.Rt.X64.code_field hp hend h11 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h12 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend h13 (Scc.Cert.Rt.X64.Print.off0 _)
  · exact Scc.Cert.Rt.X64.code_field hp hend hs rfl

end Proof

end Spike.Lib.X64.PrintA
