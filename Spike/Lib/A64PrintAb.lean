/-
**`scc_rt_print` against a byte-by-byte source, with the refusal's data**
(AArch64): `Spike/Lib/A64PrintA.lean`'s function (same blocks, same graph,
same ghosts `x29`, `ra`, `buf0`, `len0`, `P`, `Q`) with the refusal branch
of the result's classification strengthened from `writeRefused r` to
`Refusal (len0 - k) r` (`Spike/Lib/Consumer1.lean`: refused and no count
`1 … len0 - k`), the data the write abort phase `WriteAb.Ab` keeps
(`Spike/Lib/A64WriteAb.lean`: the length `[sp + 8]` refused by the result).

- `RC2`, `RC1`, `RC0`, `N`, `E`: as `PrintA`'s, `RC2`'s refusal by
  `Refusal`; the loop's invariants are `PrintA.JL`, `PrintA.JI`,
  `PrintA.JIlt`;
- `PrintAbW` (one `BlkW` per block node), `PrintAbW.triv`;
- `seg_printAbW`, `seg_printAb_ofW`: the function is one segment inside
  `W` (as `seg_printAW`, `seg_printA_ofW`);
- `refusal_of_refused`: below `2^63` bytes every refusal is a `Refusal`;
- `rc0_of_retOk`, `hsvc_of_emit`: the write system call from the output row
  (as `Spike/Lib/A64PrintEmit.lean`'s), its results classified by this
  `RC0`.

`PrintA`'s statements are unchanged; a caller picks either.
`len0 < 2^63` (entry): a positive count is then a positive signed number,
and no count `1 … len0 - k` is a refusal.
-/
import Spike.Lib.A64PrintEmit
import Spike.Lib.Consumer1

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.PrintAb

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Print
open Spike.Lib.A64.PrintA (subs_z subs0_z subs0_le pos_not_le refused_le refused_ne4 refused_ne11 adv_buf adv_len
  len_zero c4_eq c11_eq neg_large RetOk EmitW)
open Spike.Lib.Consumer1 (Refusal)
open Scc.Sem.Kernel (writeRefused neg eintr eagain results)

/-! ## The specification -/

section Spec

variable (lab : Label → Int64) (x29 ra buf0 : BitVec 64) (len0 : Nat) (P Q : Nat → Ctl → Prop)

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
  | .e => ⟨lab "scc_rt_print", oE, fun σ c => P 0 c ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
      σ.regs.X0.toBitVec = buf0 ∧ σ.regs.X1.toBitVec = BitVec.ofNat 64 len0⟩
  | .n1 => ⟨lab ".L9_scc_rt_print.0_entry", oI, PrintA.JI x29 ra buf0 len0 P⟩
  | .loop => ⟨lab ".L9_scc_rt_print.1_loop", oI, PrintA.JI x29 ra buf0 len0 P⟩
  | .n3 => ⟨lab ".L9_scc_rt_print.1_loop" + 4 + 4 + 4 + 4, oI, PrintA.JIlt x29 ra buf0 len0 P⟩
  | .write => ⟨lab ".L9_scc_rt_print.2_write", oI, PrintA.JIlt x29 ra buf0 len0 P⟩
  | .svc => ⟨Print.pcSvc lab, oI, fun σ c => PrintA.JIlt x29 ra buf0 len0 P σ c ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64 ∧
      σ.regs.X1.toBitVec = σ.slot (-48) ∧ σ.regs.X2.toBitVec = σ.slot (-40)⟩
  | .n5 => ⟨Print.pcSvc lab + 4, oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC0 len0 P Q k σ.regs.X0.toBitVec c⟩
  | .n6 => ⟨Print.pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      (∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC0 len0 P Q k (σ.slot (-32)) c) ∧
        σ.status = StatusFlags.subs (σ.slot (-32) - PrintA.C4) (σ.slot (-32)) PrintA.C4⟩
  | .n7 => ⟨Print.pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c⟩
  | .chk2 => ⟨lab ".L9_scc_rt_print.3_chk2", oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c⟩
  | .n9 => ⟨lab ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      (∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c) ∧
        σ.status = StatusFlags.subs (σ.slot (-32) - PrintA.C11) (σ.slot (-32)) PrintA.C11⟩
  | .n10 => ⟨lab ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-32)) c⟩
  | .chk3 => ⟨lab ".L9_scc_rt_print.4_chk3", oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ RC2 len0 P Q k (σ.slot (-32)) c⟩
  | .n12 => ⟨lab ".L9_scc_rt_print.4_chk3" + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ 0 < (σ.slot (-32)).toNat ∧ (σ.slot (-32)).toNat ≤ len0 - k ∧
        P (k + (σ.slot (-32)).toNat) c⟩
  | .adv => ⟨lab ".L9_scc_rt_print.5_adv", oI, fun σ c =>
      ∃ k, PrintA.JL x29 ra buf0 len0 k σ ∧ 0 < (σ.slot (-32)).toNat ∧ (σ.slot (-32)).toNat ≤ len0 - k ∧
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
structure PrintAbW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
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
theorem PrintAbW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    PrintAbW x29 ra buf0 len0 P Q (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
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
theorem seg_printAbW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hlen : len0 < 2 ^ 63)
    (hcode : Print.Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hW : PrintAbW x29 ra buf0 len0 P Q W K exe endPc R F)
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
    by_cases hz : σ.slot (-32) = PrintA.C4
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h11, -⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at h11; exact absurd h11 (by decide)
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [PrintA.C4, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne4 hw.1)
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
    by_cases hz : σ.slot (-32) = PrintA.C11
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [PrintA.C11, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne11 hw.1)
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
        rw [subs0_le]; exact refused_le hw.1
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
theorem seg_printAb_ofW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop}
    [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Scc.Cert.Rt.A64.Lays exe prog kp) (hend : endPc = Scc.Cert.Rt.A64.endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hlen : len0 < 2 ^ 63)
    (hW : PrintAbW x29 ra buf0 len0 P Q W K exe endPc R F)
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label x29 ra len0 P Q x) s c) := by
  simp only [Scc.Cert.Rt.A64.Print.printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hgap⟩ := hprog
  refine seg_printAbW (c0 := ⟨.ret .unit, [], none⟩) hF hR hal hlo hhi hlen
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

section Svc

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {x29 ra buf0 : BitVec 64}
  {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- **`scc_rt_print`'s write system call is a segment inside `W`** from
`.svc` to `.n5`, as `PrintA.hsvc_of_emit` (same premises), each result
classified by this `RC0` (`rc0_of_retOk`). -/
theorem hsvc_of_emit {W : Frag isaLSE2} {K : State → State → Prop}
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).pc [svcDir])
    (hW : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c →
      W s c ∧ ∀ s', ¬ K s s')
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → BO s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c →
      ∀ k c1, Q k c1 → WE s c1) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5)) := by
  refine hE _ _ hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨k, hL, hk, hP⟩, h0, h8, h1, h2⟩ := id hAt
  obtain ⟨h16, h8', h48, h40, hkl⟩ := hL
  have hl := hlen k c hP
  have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hx1 : s.st.1.regs.X1.toNat = (buf0 + BitVec.ofNat 64 k).toNat := by
    rw [hA.regs, ← h48, ← h1]; rfl
  have hx2 : s.st.1.regs.X2.toNat = len0 - k := by
    rw [hA.regs, UInt64.toNat, h2, h40, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.write 1 (buf0 + BitVec.ofNat 64 k).toNat (len0 - k)) := by
    have hr0 : s.st.1.regs.X0 = 1 := by rw [hA.regs]; exact h0
    have hr8 : s.st.1.regs.X8 = 64 := by rw [hA.regs]; exact h8
    simp [Scc.Sem.A64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, hr0, hr8, ← hx1,
      ← hx2]
  refine ⟨_, _, fun j c1 => P (k + j) c1, Q k, hK, Scc.Sem.A64.atSvc_of_cellAt hc, hd, ⟨c, .refl c, hP⟩,
    fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h, fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩,
    fun c1 h => hwe s c hAt k c1 h⟩
  · rw [Scc.Sem.A64.abi_ret_of_cellAt hc r]
    have hA' : Flow.Abs R oI { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } }
        (svcStep r σ) := by
      refine Flow.Abs.weaken (o' := oI) (o := oI.kill .X0) (by decide)
        ⟨by simp only [svcStep, hA.regs], hA.status, ?_, hA.slot⟩
      refine hA.so.kill .X0 fun r hr => ?_
      rcases r with y | _
      · cases y <;> first | rfl | exact absurd rfl hr
      · rfl
    have hD' : F { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } } :=
      hF _ _ hD fun _ _ _ => rfl
    refine ⟨he, hn, hdc, ?_, svcStep r σ, hA', hD', k, ⟨h16, h8', h48, h40, hkl⟩, ?_⟩
    · simp only [svcRet, after, hpc]; rfl
    · have hx0 : (svcStep r σ).regs.X0.toBitVec = r := by simp [svcStep]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
  · subst hj0; exact hPQ k c1 hPj

end Svc

end Spike.Lib.A64.PrintAb
