/-
**`scc_rt_print` against a byte-by-byte source, with the refusal's data**
(x64): `Spike/Lib/X64PrintA.lean`'s function (same blocks, same graph, same
ghosts `rbp0`, `ra`, `buf0`, `len0`, `P`, `Q`) with the refusal branch of
the result's classification strengthened from `writeRefused r` to
`Refusal (len0 - k) r` (`Spike/Lib/Consumer1.lean`), the data the write
abort phase `WriteAb.Ab` keeps (`Spike/Lib/X64WriteAb.lean`: the length
`-16(%rbp)` refused by the result): the x64 twin of
`Spike/Lib/A64PrintAb.lean`.

- `RC2`, `RC1`, `RC0`, `N`, `E`: as `PrintA`'s, `RC2`'s refusal by
  `Refusal`; the loop's invariants are `PrintA.JL`, `PrintA.JI`,
  `PrintA.JIlt`;
- `PrintAbW` (one `BlkW` per block node), `PrintAbW.triv`;
- `seg_printAbW`, `seg_printAb_ofW`: the function is one segment inside
  `W` (as `seg_printAW`, `seg_printA_ofW`);
- `refusal_of_refused`: below `2^63` bytes every refusal is a `Refusal`;
- `rc0_of_retOk`, `hsys_of_emit`: the write system call from the output row
  (as `Spike/Lib/X64PrintEmit.lean`'s), its results classified by this
  `RC0`.

`PrintA`'s statements are unchanged; a caller picks either.
`len0 < 2^63` (entry): a positive count is then a positive signed number,
and no count `1 … len0 - k` is a refusal.
-/
import Spike.Lib.X64PrintEmit
import Spike.Lib.Consumer1

set_option linter.unusedSimpArgs false

namespace Spike.Lib.X64.PrintAb

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Spike.Lib.X64.Print (PN PX x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI oE pcSys
  x0_ok x1_ok x2_ok x3_ok x4_ok x5_ok x6_ok x7_ok x8_ok x9_ok x10_ok x11_ok x12_ok x13_ok
  x0_run x1_run x2_run x3_run x4_run x5_run x6_run x7_run x8_run x9_run x10_run x11_run x12_run x13_run)
open Spike.Lib.X64.PrintA (pos_not_le refused_le refused_ne4 refused_ne11 adv_buf adv_len len_zero sub_z
  c4_eq c11_eq RetOk EmitW)
open Spike.Lib.Consumer1 (Refusal)
open Scc.Sem.Kernel (writeRefused neg eintr eagain results)

/-! ## The specification -/

section Spec

variable (lab : Label → Int64) (rbp0 ra buf0 : BitVec 64) (len0 : Nat) (P Q : Nat → Ctl → Prop)

/-- A positive count `r`: `r` more bytes out; or a refusal of the `len0 - k`
bytes left (`Refusal`: no count `1 … len0 - k`). -/
def RC2 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop :=
  (0 < r.toNat ∧ r.toNat ≤ len0 - k ∧ P (k + r.toNat) c) ∨ (Refusal (len0 - k) r ∧ Q k c)

/-- The result past the `-EINTR` check. -/
def RC1 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop := (r = PrintA.C11 ∧ P k c) ∨ RC2 len0 P Q k r c

/-- **What the system call returns**: `-EINTR`/`-EAGAIN` with the source
unmoved, a positive count with the source `r` bytes further, or a refusal
justifying the abort. -/
def RC0 (k : Nat) (r : BitVec 64) (c : Ctl) : Prop := (r = PrintA.C4 ∧ P k c) ∨ RC1 len0 P Q k r c

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_print", oE, fun σ c => P 0 c ∧ σ.regs.rbp.toBitVec = rbp0 ∧ σ.slot 8 = ra ∧
      σ.regs.get64 .rdi = buf0 ∧ σ.regs.get64 .rsi = BitVec.ofNat 64 len0⟩
  | .n1 => ⟨lab ".Lscc_rt_print.entry", oI, PrintA.JI rbp0 ra buf0 len0 P⟩
  | .loop => ⟨lab ".Lscc_rt_print.loop", oI, PrintA.JI rbp0 ra buf0 len0 P⟩
  | .n3 => ⟨lab ".Lscc_rt_print.loop" + 20, oI, PrintA.JIlt rbp0 ra buf0 len0 P⟩
  | .write => ⟨lab ".Lscc_rt_print.write", oI, PrintA.JIlt rbp0 ra buf0 len0 P⟩
  | .sys => ⟨pcSys lab, oI, fun σ c => PrintA.JIlt rbp0 ra buf0 len0 P σ c ∧ σ.regs.get64 .rdi = 1 ∧
      σ.regs.get64 .rax = 1 ∧ σ.regs.get64 .rsi = σ.slot (-8) ∧ σ.regs.get64 .rdx = σ.slot (-16)⟩
  | .n5 => ⟨lab ".Lscc_rt_print.write" + 22, oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ RC0 len0 P Q k (σ.regs.get64 .rax) c⟩
  | .n6 => ⟨lab ".Lscc_rt_print.write" + 42, oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-24)) c⟩
  | .chk2 => ⟨lab ".Lscc_rt_print.chk2", oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-24)) c⟩
  | .n8 => ⟨lab ".Lscc_rt_print.chk2" + 16, oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-24)) c⟩
  | .chk3 => ⟨lab ".Lscc_rt_print.chk3", oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-24)) c⟩
  | .n10 => ⟨lab ".Lscc_rt_print.chk3" + 16, oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ 0 < (σ.slot (-24)).toNat ∧ (σ.slot (-24)).toNat ≤ len0 - k ∧
        P (k + (σ.slot (-24)).toNat) c⟩
  | .adv => ⟨lab ".Lscc_rt_print.adv", oI, fun σ c =>
      ∃ k, PrintA.JL rbp0 ra buf0 len0 k σ ∧ 0 < (σ.slot (-24)).toNat ∧ (σ.slot (-24)).toNat ≤ len0 - k ∧
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
structure PrintAbW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
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
theorem PrintAbW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    PrintAbW rbp0 ra buf0 len0 P Q (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
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
theorem seg_printAbW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hcode : Print.Code c0 rbp0 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hW : PrintAbW rbp0 ra buf0 len0 P Q W K exe endPc R F)
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
    have hL' : PrintA.JL rbp0 ra buf0 len0 k { σ with slot := Spike.Lib.upd σ.slot (-24) σ.regs.rax.toBitVec } := by
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
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [PrintA.C4, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne4 hw.1)
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
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [PrintA.C11, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne11 hw.1)
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
      · exact absurd (refused_le hw.1).symm hn
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
theorem seg_printAb_ofW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop}
    [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Scc.Cert.Rt.X64.Lays exe cells kp) (hend : endPc = Scc.Cert.Rt.X64.endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hW : PrintAbW rbp0 ra buf0 len0 P Q W K exe endPc R F)
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label rbp0 ra len0 P Q x) s c) := by
  simp only [Scc.Cert.Rt.X64.Print.printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, hgap⟩ := hprog
  refine seg_printAbW (c0 := ⟨.ret .unit, [], none⟩) hF hR hlo hhi hlen
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

/-! ## The refusal's data -/

/-- **Below `2^63` bytes a refusal is a `Refusal`**: a refused result is
zero or at least `2^64 - 4095`, no count `1 … n`. -/
theorem refusal_of_refused {n : Nat} {r : BitVec 64} (hn : n < 2 ^ 63) (h : writeRefused r = true) :
    Refusal n r := by
  refine ⟨h, fun j hj hjn hr => ?_⟩
  subst hr
  have hj' : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rcases refused_le h with h0 | hm
  · have := congrArg BitVec.toNat h0; rw [hj'] at this; simp at this; omega
  · rw [BitVec.msb_eq_decide, hj'] at hm; simp at hm; omega

/-- **A result the kernel may return is one `RC0` admits**, the source at
`P (k + j)` after `j ≤ len0 - k` bytes. -/
theorem rc0_of_retOk {len0 k j : Nat} {P Q : Nat → Ctl → Prop} {r : BitVec 64} {c : Ctl} (hlen : len0 < 2 ^ 63)
    (hj : j ≤ len0 - k) (hPQ : P k c → Q k c) (hP : P (k + j) c) (hr : RetOk j r) : RC0 len0 P Q k r c := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rcases hr.2 rfl with h | h | h
    · exact .inl ⟨h.trans c4_eq.symm, hP⟩
    · exact .inr (.inl ⟨h.trans c11_eq.symm, hP⟩)
    · exact .inr (.inr (.inr ⟨refusal_of_refused (by omega) h, hPQ hP⟩))
  · have hr' := hr.1 hpos
    have hn : r.toNat = j := by rw [hr', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact .inr (.inr (.inl ⟨by omega, by omega, by rw [hn]; exact hP⟩))

/-! ## The system call -/

section Sys

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {rbp0 ra buf0 : BitVec 64}
  {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- **`scc_rt_print`'s write system call is a segment inside `W`** from
`.sys` to `.n5`, as `PrintA.hsys_of_emit` (same premises), each result
classified by this `RC0` (`rc0_of_retOk`). -/
theorem hsys_of_emit {W : Frag isa} {K : State → State → Prop}
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).pc
        [(.instr (.regular .W64 .W64 .syscall), 2)])
    (hW : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c →
      W s c ∧ ∀ s', ¬ K s s')
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → BO s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c →
      ∀ k c1, Q k c1 → WE s c1) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5)) := by
  refine hE _ _ hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨k, hL, hk, hP⟩, hdi, hax, hsi, hdx⟩ := id hAt
  obtain ⟨h0, h8, h16, h24, hkl⟩ := hL
  have hl := hlen k c hP
  have hc : CellAt s (.instr (.regular .W64 .W64 .syscall)) 2 := (hcode s he hn).cell0 rfl rfl hpc
  have hrax : s.st.1.regs.rax.toNat = 1 := by
    have : s.st.1.regs.get64 .rax = 1 := by rw [hA.regs]; exact hax
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]; rfl
  have hrdi : s.st.1.regs.rdi.toNat = 1 := by
    have : s.st.1.regs.get64 .rdi = 1 := by rw [hA.regs]; exact hdi
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]; rfl
  have hrsi : s.st.1.regs.rsi.toNat = (buf0 + BitVec.ofNat 64 k).toNat := by
    have : s.st.1.regs.get64 .rsi = buf0 + BitVec.ofNat 64 k := by rw [hA.regs, hsi, h16]
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]
  have hrdx : s.st.1.regs.rdx.toNat = len0 - k := by
    have : s.st.1.regs.get64 .rdx = BitVec.ofNat 64 (len0 - k) := by rw [hA.regs, hdx, h24]
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.write 1 (buf0 + BitVec.ofNat 64 k).toNat (len0 - k)) := by
    simp [Scc.Sem.X64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, hrax, hrdi, hrsi, hrdx]
  refine ⟨_, _, fun j c1 => P (k + j) c1, Q k, hK, Scc.Sem.X64.atSyscall_of_cellAt hc, hd, ⟨c, .refl c, hP⟩,
    fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h, fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩,
    fun c1 h => hwe s c hAt k c1 h⟩
  · rw [Scc.Sem.X64.abi_ret_of_cellAt hc r]
    let pc' := (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).pc + Int64.ofNat 2
    have hA' : Abs R oI { s.st.1 with regs := syscallRegs pc' (Scc.Sem.X64.rflags σ.status) r s.st.1.regs }
        (syscallStep pc' r σ) :=
      Abs.weaken (o := syscallSO oI) (by decide)
        ⟨by simp only [syscallStep, hA.regs], hA.zmms, hA.status, syscallSO_rel hA.so _ _ _, hA.slot⟩
    have hD' : F { s.st.1 with regs := syscallRegs pc' (Scc.Sem.X64.rflags σ.status) r s.st.1.regs } :=
      hF _ _ hD fun _ _ _ => rfl
    have hs1 : syscallRet s 2 (Scc.Sem.X64.kret (Scc.Sem.X64.rflags s.st.1.status) (syscallInfo s 2) r) =
        { s with st := ({ s.st.1 with regs := syscallRegs pc' (Scc.Sem.X64.rflags σ.status) r s.st.1.regs },
          pc') } := by
      simp only [syscallRet, after, Scc.Sem.X64.kret, syscallRegs, hpc, hA.status, pc']
    rw [hs1]
    refine ⟨he, hn, hdc, ?_, syscallStep pc' r σ, hA', hD', k, ⟨h0, h8, h16, h24, hkl⟩, ?_⟩
    · show pc' = _
      simp only [pc', N, pcSys, Int64.add_assoc]; rfl
    · have hx0 : (syscallStep pc' r σ).regs.get64 .rax = r := by
        simp [syscallStep, syscallRegs, Reg64s.get64]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
  · subst hj0; exact hPQ k c1 hPj

end Sys

end Spike.Lib.X64.PrintAb
