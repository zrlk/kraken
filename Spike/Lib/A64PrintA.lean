/-
**`scc_rt_print` against a source that prints byte by byte** (AArch64):
the function of `Spike/Lib/A64Print.lean` (same blocks, same graph) with
invariants that track how far the output has got, for a source whose
`print` is an emit loop.

Ghost parameters: the caller's `x29`, the return address `ra`, the buffer's
address `buf0` and length `len0` at entry, and two predicates on the source
control: `P k` (the source has printed the first `k` bytes and is ready
for byte `k`) and `Q k` (after `k` bytes, a refused write justifies the
abort). Inside the loop the frame's cells hold `buf0 + k` and `len0 - k` for
some `k ≤ len0` with `P k` (`JL`, `JI`).

The `write` system call is a given node (`hsvc`). From the loop's state
with `k < len0`, `x1 = buf0 + k`, `x2 = len0 - k`, it returns to the next
instruction with the frame's cells kept and a result `r` in `x0`, which
`RC0` classifies:

- `-EINTR`/`-EAGAIN`: the source has not moved (`P k`);
- `0 < r ≤ len0 - k`: the source has printed `r` more bytes (`P (k + r)`);
- a refusal (`writeRefused`): `Q k`.

Every block node keeps the source where it is: only the system call moves
it. A caller discharges `hsvc` with the kernel's write steps and the source's
byte steps (one `out` each). The specification:

- **entry** (`.e`): `P 0`, `x0 = buf0`, `x1 = len0`, `x29`, `x30 = ra`;
- **return** (`.ret`): pc at `ra`, `x29`, `x30` restored, `P len0`;
- **abort** (`.abort`): pc at `scc_rt_abort`, `x0 = 4`, `Q k` for some `k`.

`len0 < 2^63`: a positive count is then a positive signed number, so the
code's `b.le` separates it from a refusal.
-/
import Spike.Lib.A64Print
import Scc.Cert.Rt.A64Print

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.PrintA

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Spike.Lib.A64.Print
open Scc.Sem.Kernel (writeRefused neg eintr eagain)

/-! ## Flags and arithmetic -/

/-- `-4` (`-EINTR`), as the code builds it. -/
abbrev C4 : BitVec 64 := 18446744073709551612#64
/-- `-11` (`-EAGAIN`), as the code builds it. -/
abbrev C11 : BitVec 64 := 18446744073709551605#64

theorem c4_eq : C4 = neg eintr := by decide
theorem c11_eq : C11 = neg eagain := by decide

/-- `subs`'s zero flag: equal operands. -/
theorem subs_z (a b : BitVec 64) : (StatusFlags.subs (a - b) a b).z = decide (a = b) := by
  simp only [StatusFlags.subs, StatusFlags.from_result]
  by_cases h : a = b
  · subst h; simp
  · simp [h, BitVec.zero_eq]; intro h'; exact h (by bv_omega)

/-- `cmp x, #0`'s zero flag. -/
theorem subs0_z (a : BitVec 64) : (StatusFlags.subs a a 0#64).z = decide (a = 0#64) := by
  simp only [StatusFlags.subs, StatusFlags.from_result, BitVec.zero_eq]
  by_cases h : a = 0#64 <;> simp [h]

/-- `cmp x, #0; b.le`: zero or negative. -/
theorem subs0_le (a : BitVec 64) :
    ((StatusFlags.subs a a 0#64).z = true ∨ ¬(StatusFlags.subs a a 0#64).n = (StatusFlags.subs a a 0#64).v) ↔
      (a = 0#64 ∨ a.msb = true) := by
  simp [StatusFlags.subs, StatusFlags.from_result, BitVec.zero_eq, BitVec.signed]

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

/-! ## The specification -/

section Spec

variable (lab : Label → Int64) (x29 ra buf0 : BitVec 64) (len0 : Nat) (P Q : Nat → Ctl → Prop)

/-- The frame's cells after `k` bytes: the caller's `x29`, the return
address, the cursor and the remaining length. -/
def JL (k : Nat) (σ : Flow.AS) : Prop :=
  σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-48) = buf0 + BitVec.ofNat 64 k ∧
    σ.slot (-40) = BitVec.ofNat 64 (len0 - k) ∧ k ≤ len0

/-- The loop's invariant: `k` bytes out, the source ready for byte `k`. -/
def JI (σ : Flow.AS) (c : Ctl) : Prop := ∃ k, JL x29 ra buf0 len0 k σ ∧ P k c

/-- The loop's invariant with bytes left. -/
def JIlt (σ : Flow.AS) (c : Ctl) : Prop := ∃ k, JL x29 ra buf0 len0 k σ ∧ k < len0 ∧ P k c

/-- A positive count `r`: `r` more bytes out. -/
def RC2 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop :=
  (0 < r.toNat ∧ r.toNat ≤ len0 - k ∧ P (k + r.toNat) c) ∨ (writeRefused r = true ∧ Q k c)

/-- The result past the `-EINTR` check. -/
def RC1 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop := (r = C11 ∧ P k c) ∨ RC2 len0 P Q k r c

/-- **What the system call returns**: `-EINTR`/`-EAGAIN` with the source
unmoved, a positive count with the source `r` bytes further, or a refusal
justifying the abort. -/
def RC0 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop := (r = C4 ∧ P k c) ∨ RC1 len0 P Q k r c

/-- The pc after the system call's argument block. -/
abbrev pcSvc : Int64 := lab ".L9_scc_rt_print.2_write" + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_print", oE, fun σ c => P 0 c ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
      σ.regs.X0.toBitVec = buf0 ∧ σ.regs.X1.toBitVec = BitVec.ofNat 64 len0⟩
  | .n1 => ⟨lab ".L9_scc_rt_print.0_entry", oI, JI x29 ra buf0 len0 P⟩
  | .loop => ⟨lab ".L9_scc_rt_print.1_loop", oI, JI x29 ra buf0 len0 P⟩
  | .n3 => ⟨lab ".L9_scc_rt_print.1_loop" + 4 + 4 + 4 + 4, oI, JIlt x29 ra buf0 len0 P⟩
  | .write => ⟨lab ".L9_scc_rt_print.2_write", oI, JIlt x29 ra buf0 len0 P⟩
  | .svc => ⟨pcSvc lab, oI, fun σ c => JIlt x29 ra buf0 len0 P σ c ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64 ∧
      σ.regs.X1.toBitVec = σ.slot (-48) ∧ σ.regs.X2.toBitVec = σ.slot (-40)⟩
  | .n5 => ⟨pcSvc lab + 4, oI, fun σ c => ∃ k, JL x29 ra buf0 len0 k σ ∧ RC0 len0 P Q k σ.regs.X0.toBitVec c⟩
  | .n6 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      (∃ k, JL x29 ra buf0 len0 k σ ∧ RC0 len0 P Q k (σ.slot (-32)) c) ∧
        σ.status = StatusFlags.subs (σ.slot (-32) - C4) (σ.slot (-32)) C4⟩
  | .n7 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c⟩
  | .chk2 => ⟨lab ".L9_scc_rt_print.3_chk2", oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c⟩
  | .n9 => ⟨lab ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      (∃ k, JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c) ∧
        σ.status = StatusFlags.subs (σ.slot (-32) - C11) (σ.slot (-32)) C11⟩
  | .n10 => ⟨lab ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-32)) c⟩
  | .chk3 => ⟨lab ".L9_scc_rt_print.4_chk3", oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-32)) c⟩
  | .n12 => ⟨lab ".L9_scc_rt_print.4_chk3" + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ 0 < (σ.slot (-32)).toNat ∧ (σ.slot (-32)).toNat ≤ len0 - k ∧
        P (k + (σ.slot (-32)).toNat) c⟩
  | .adv => ⟨lab ".L9_scc_rt_print.5_adv", oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ 0 < (σ.slot (-32)).toNat ∧ (σ.slot (-32)).toNat ≤ len0 - k ∧
        P (k + (σ.slot (-32)).toNat) c⟩
  | .fail => ⟨lab ".L9_scc_rt_print.6_fail", oI, fun _ c => ∃ k, Q k c⟩
  | .done => ⟨lab ".L9_scc_rt_print.7_done", oI, fun σ c => σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ P len0 c⟩

/-- **The exits**: the return to `ra` with `x29` and `x30` restored and all
`len0` bytes out, and the abort with code 4 after a refusal. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, fun σ c => σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧ P len0 c⟩
  | .abort => ⟨lab "scc_rt_abort", oI, fun σ c => σ.regs.X0 = 4 ∧ ∃ k, Q k c⟩

/-- **The function's states inside `W`**, none moved by `K`: one obligation
per block node (the system call is a given node). -/
structure PrintAW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e) b0
  n1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n1) b1
  loop : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .loop) b2
  n3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n3) b3
  write : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .write) b4
  n5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5) b5
  n6 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n6) b6
  n7 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n7) b7
  chk2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .chk2) b8
  n9 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n9) b9
  n10 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n10) b10
  chk3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .chk3) b11
  n12 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n12) b12
  adv : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .adv) b13
  fail : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .fail) b14
  done : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .done) b16

/-- The function is inside the trivial predicate, with no outside moves. -/
theorem PrintAW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    PrintAW x29 ra buf0 len0 P Q (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv⟩

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {c0 : Ctl} {x29 ra buf0 : BitVec 64} {len0 : Nat}
  {P Q : Nat → Ctl → Prop}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code, its `W` obligation; the
source stays; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) hW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- Hitting node `j`: the pc and offsets; the invariant is left, unfolded. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> try simp only [N]) <;> try first | rfl | exact hentry)

/-- Hitting exit `x`: the offsets; the pc and the invariant are left. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> try simp only [E]) <;> try rfl)

set_option maxHeartbeats 1000000 in
/-- **`scc_rt_print` is one segment inside `W`** from its entry to its
return or its abort, against a source that prints byte by byte: the block
nodes keep the source where it is, and the system call (`hsvc`, a given
segment inside `W`) moves it by the count it returns. The code is
`seg_printW`'s (`Print.Code`, any `c0`). -/
theorem seg_printAW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hlen : len0 < 2 ^ 63)
    (hcode : Print.Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hW : PrintAW x29 ra buf0 len0 P Q W K exe endPc R F)
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label x29 ra len0 P Q x) s c) := by
  have hl64 : len0 < 2 ^ 64 := by omega
  refine fn_segW (N := N _ x29 ra buf0 len0 P Q) (E := E _ x29 ra len0 P Q) (fun i => ?_) PN.e
  cases i
  case svc => exact seg_givenW PN.n5 hsvc
  case e =>
    node b0 b0_ok e; rw [N, b0_run]; hit PN.n1
    obtain ⟨hP, h29, h30, h0, h1⟩ := hJ
    exact ⟨0, ⟨by simp [Spike.Lib.upd_apply, h29], by simp [Spike.Lib.upd_apply, h30],
      by simp [Spike.Lib.upd_apply, h0], by simp [Spike.Lib.upd_apply, h1], Nat.zero_le _⟩, hP⟩
  case n1 => node b1 b1_ok n1; rw [N, b1_run]; hit PN.loop; exact hJ
  case loop =>
    node b2 b2_ok loop; rw [N, b2_run]
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, hP⟩ := hJ
    simp only [subs0_z, h40]
    by_cases hz : k = len0
    · subst hz
      simp only [Nat.sub_self, decide_true, ite_true]
      hit PN.done
      exact ⟨h16, h8, hP⟩
    · have hz' : ¬ BitVec.ofNat 64 (len0 - k) = 0#64 := fun h => hz ((len_zero hl64 hk).1 h)
      simp only [hz', decide_false, Bool.false_eq_true, ite_false]
      hit PN.n3
      exact ⟨k, ⟨h16, h8, h48, h40, hk⟩, by omega, hP⟩
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.write; exact hJ
  case write =>
    node b4 b4_ok write; rw [N, b4_run]; hit PN.svc
    refine ⟨hJ, ?_⟩
    simp
  case n5 =>
    node b5 b5_ok n5; rw [N, b5_run]; hit PN.n6
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, hr⟩ := hJ
    refine ⟨⟨k, ⟨?_, ?_, ?_, ?_, hk⟩, ?_⟩, ?_⟩
    · simp [Spike.Lib.upd_apply, h16]
    · simp [Spike.Lib.upd_apply, h8]
    · simp [Spike.Lib.upd_apply, h48]
    · simp [Spike.Lib.upd_apply, h40]
    · simpa [Spike.Lib.upd_apply] using hr
    · simp only [Spike.Lib.upd_apply, ite_true]
  case n6 =>
    node b6 b6_ok n6; rw [N, b6_run]
    obtain ⟨⟨k, hL, hr⟩, hs⟩ := hJ
    simp only [hs, subs_z]
    by_cases hz : σ.slot (-32) = C4
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h11, -⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at h11; exact absurd h11 (by decide)
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C4, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne4 hw)
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      hit PN.n7
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h4, -⟩ | h
      · exact absurd h4 hz
      · exact h
  case n7 => node b7 b7_ok n7; rw [N, b7_run]; hit PN.chk2; exact hJ
  case chk2 =>
    node b8 b8_ok chk2; rw [N, b8_run]; hit PN.n9
    exact ⟨hJ, trivial⟩
  case n9 =>
    node b9 b9_ok n9; rw [N, b9_run]
    obtain ⟨⟨k, hL, hr⟩, hs⟩ := hJ
    simp only [hs, subs_z]
    by_cases hz : σ.slot (-32) = C11
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C11, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne11 hw)
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      hit PN.n10
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h11, -⟩ | h
      · exact absurd h11 hz
      · exact h
  case n10 => node b10 b10_ok n10; rw [N, b10_run]; hit PN.chk3; exact hJ
  case chk3 =>
    node b11 b11_ok chk3; rw [N, b11_run]
    obtain ⟨k, hL, hr⟩ := hJ
    rcases hr with ⟨h0, hle, hP⟩ | ⟨hw, hQ⟩
    · have hn : ¬ ((StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).z = true ∨
          ¬(StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).n =
            (StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).v) := by
        rw [subs0_le]; exact pos_not_le h0 (by omega)
      simp only [hn, ite_false]
      hit PN.n12
      exact ⟨k, hL, h0, hle, hP⟩
    · have hy : ((StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).z = true ∨
          ¬(StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).n =
            (StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).v) := by
        rw [subs0_le]; exact refused_le hw
      simp only [hy, ite_true]
      hit PN.fail
      exact ⟨k, hQ⟩
  case n12 => node b12 b12_ok n12; rw [N, b12_run]; hit PN.adv; exact hJ
  case adv =>
    node b13 b13_ok adv; rw [N, b13_run]; hit PN.loop
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, h0, hle, hP⟩ := hJ
    refine ⟨k + (σ.slot (-32)).toNat, ⟨?_, ?_, ?_, ?_, by omega⟩, hP⟩
    · simp [Spike.Lib.upd_apply, h16]
    · simp [Spike.Lib.upd_apply, h8]
    · simp only [Spike.Lib.upd_apply]; simp only [show (-48 : Int) ≠ -40 by decide, ite_true, ite_false]
      rw [h48, adv_buf]
    · simp only [Spike.Lib.upd_apply, ite_true]; rw [h40, adv_len hl64 hle]
  case fail =>
    node b14 b14_ok fail; rw [N, b14_run]; exit PX.abort
    exact ⟨by trivial, hJ⟩
  case done =>
    node b16 b16_ok done; rw [N, b16_run]; exit PX.ret
    · rw [hJ.2.1]
    · exact ⟨hJ.1, hJ.2.1, hJ.2.2⟩

/-- **`scc_rt_print` is one segment inside `W`** against a byte-by-byte
source in any valid layout `exe` of a program `prog` with
`printIn prog = true` (`SccCode.hello1_print` for `hello1Prog`), given its
write system call (`hsvc`). -/
theorem seg_printA_ofW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop}
    [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Scc.Cert.Rt.A64.Lays exe prog kp) (hend : endPc = Scc.Cert.Rt.A64.endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hlen : len0 < 2 ^ 63)
    (hW : PrintAW x29 ra buf0 len0 P Q W K exe endPc R F)
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label x29 ra len0 P Q x) s c) := by
  simp only [Scc.Cert.Rt.A64.Print.printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hgap⟩ := hprog
  refine seg_printAW (c0 := ⟨.ret .unit, [], none⟩) hF hR hal hlo hhi hlen
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [Scc.Cert.Rt.A64.label_labelGap hp hgap]
        simp only [Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0]) hW hsvc
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h0
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h1
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h2
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h3
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h4
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h5
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h6
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h7
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h8
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h9
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h10
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h11
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h12
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h13
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h14
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend h15
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend hs
      (by simp only [Print.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])

end Proof

end Spike.Lib.A64.PrintA
