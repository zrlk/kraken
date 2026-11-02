/-
**hello.w's `scc_rt_print` off the transfer sites on x86-64** (the twin of `Spike/Lib/A64HelloPrintNN.lean`):
the per-node blocks of x86-64's `scc_rt_print` (`Spike/Lib/X64Print.lean`'s nodes `Print.N` and code
`Print.Code`, the facts hello's `wc_worker` gives `print` at `helloCells`: `Hello.Wk.printCode`), the `blk` of
each node's `NodeZA` obligation.

- `PrintF.FA.blkN`: each node's block (the single `syscall` at `.sys`).
- `PrintF.FA.blkN_sys`: the `syscall` node's block.
- `PrintF.FA.seg_printFANN`: `PrintF.FA.seg_printFA` (`Spike/Lib/X64HelloPrintFramesJ.lean`) over
  `SegTC (NNZP Sy exe endPc Z)` (`Spike/Lib/X64HelloNN.lean`): every state of its hidden invariants at a cell
  other than a `nop`, its system call in `Sy`, `Z` at each node's states (`hZ`, per node a
  `NodeZA Z exe endPc R F ((N i).withTp tp) (blkN i)`), the `write` a given node.
- `PrintF.FA.hsvc_of_emitTNN`: that node from the output row, inside `NNZP SysW1` (`%rax = 1`, `%rdi = 1`
  decode to a `write` to fd 1; `nodeW_nnzPSvcA`), `Z` at it.

The proofs are `X64HelloPrintFramesJ`'s with the leaves `seg_ndNNPA` and `step_ndNNP`/`nodeW_nnzPSvcA`.

## Differences from the AArch64 version

- The nodes are x86-64's `Print.PN` (15, no fence; the `write` system call `.sys`), the blocks sized cells
  (`Print.x0 … x13`); A64's `lenN`, `lenN_eq` have no twin (`NodeZA` is indexed by the block).
- No fence: no `dmb_ndNNPA` case; the `write`'s node is `.sys` (A64's `.svc`), its block the `syscall`; the
  region is `[-40, 16]` (`hlo : R.lo ≤ -40`, `hhi : 16 ≤ R.hi`; A64's `-48`, `0`), no `hal`; the code is
  `Print.Code` and `.entry` is `scc_rt_print + 16` (as `X64HelloPrintFramesJ`'s `seg_printFA`); the thread
  pointer is the `%fs` base (`arun_fsBase`; A64's `TPIDR_EL0`).
- A64's `seg_printFAH`, `printF_callTNN` (dead) are not twinned.
-/
import Spike.Lib.X64Print
import Spike.Lib.X64HelloPrintFramesJ
import Spike.Lib.X64HelloNN

set_option linter.unusedSimpArgs false

namespace Spike.Lib.X64.Flow.Worker.PrintF.FA

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Print (PN)

/-- Each node's block (the `syscall` at `.sys`), the `blk` of its `NodeZA` obligation. -/
def blkN : PN → List (Directive × Nat)
  | .e => Print.x0 | .n1 => Print.x1 | .loop => Print.x2 | .n3 => Print.x3 | .write => Print.x4
  | .sys => [(.instr (.regular .W64 .W64 .syscall), 2)] | .n5 => Print.x5 | .n6 => Print.x6
  | .chk2 => Print.x7 | .n8 => Print.x8 | .chk3 => Print.x9 | .n10 => Print.x10 | .adv => Print.x11
  | .fail => Print.x12 | .done => Print.x13

/-- The `write` system call's node is the single `syscall`. -/
theorem blkN_sys : blkN .sys = [(.instr (.regular .W64 .W64 .syscall), 2)] := rfl

section ProofNN

open CoreLang CoreTerm
open Kraken.Promising.Lower.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Worker (NNZP SysW1 NodeZA seg_ndNNPA step_ndNNP nodeW_nnzPSvcA notNop fn_segTS)
open Spike.Lib.X64.Print (PX x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI pcSys
  x0_ok x1_ok x2_ok x3_ok x4_ok x5_ok x6_ok x7_ok x8_ok x9_ok x10_ok x11_ok x12_ok x13_ok
  x0_run x1_run x2_run x3_run x4_run x5_run x6_run x7_run x8_run x9_run x10_run x11_run x12_run x13_run)
open Spike.Lib.X64.PrintA (N E JL RC0 C4 C11 len_zero sub_z pos_not_le refused_le refused_ne4
  refused_ne11 adv_buf adv_len rc0_of_retOk)
open Spike.Lib.X64.Flow.Worker.PrintF (lands_withTp)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop} {tp : UInt64}
  {Sy : Scc.Sem.Kernel.Call → Prop} {Z : Frag isa}

set_option hygiene false in
/-- A block node with the thread pointer off the transfer sites: the block,
its `okBlk`, its code, `Z` at its states (`hZ i`); the edge (without the
thread pointer) is left, the invariant in `hJ`. -/
local macro "pnode " b:ident ok:ident f:ident i:term : tactic =>
  `(tactic| (refine (seg_ndNNPA (blk := $b:ident) (by simp [$b:ident]) $ok (by decide) hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJt => ⟨c, .refl c,
      lands_withTp (by rw [arun_fsBase]; exact hJt.2) ?_⟩) (hZ $i)); have hJ := hJt.1; dsimp only [ND.withTp]))

set_option maxHeartbeats 1000000 in
/-- **`seg_printFA` off the transfer sites** (`hsvc` over
`SegTC (NNZP Sy …)`, `Z` at each node's states: `hZ`). -/
theorem seg_printFANN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hlen : len0 < 2 ^ 63) (hcode : Print.Code c0 rbp0 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hsvc : SegTC (NNZP Sy exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5).withTp tp)))
    (hZ : ∀ i, NodeZA Z exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q i).withTp tp)
      (blkN i)) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .e).withTp tp))
      (fun s c => ∃ x, At exe endPc R F
        ((E (_root_.Executable.labels exe).label rbp0 ra len0 P Q x).withTp tp) s c) := by
  have hl64 : len0 < 2 ^ 64 := by omega
  refine fn_segTS (N := fun i => (N _ rbp0 ra buf0 len0 P Q i).withTp tp)
    (E := fun x => (E _ rbp0 ra len0 P Q x).withTp tp) (fun i => ?_) PN.e
  cases i
  case sys => exact hsvc.mono_post fun _ _ h => .inl ⟨PN.n5, h⟩
  case e =>
    pnode x0 x0_ok e PN.e; rw [N, x0_run]; hit PN.n1
    obtain ⟨hP, hbp, h8, h0, h1⟩ := hJ
    exact ⟨0, ⟨by simp [Spike.Lib.upd_apply, hbp], by simp [Spike.Lib.upd_apply, h8],
      by simp [Spike.Lib.upd_apply]; exact h0, by simp [Spike.Lib.upd_apply]; exact h1, Nat.zero_le _⟩, hP⟩
  case n1 => pnode x1 x1_ok n1 PN.n1; rw [N, x1_run]; hit PN.loop; exact hJ
  case loop =>
    pnode x2 x2_ok loop PN.loop; rw [N, x2_run]
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
  case n3 => pnode x3 x3_ok n3 PN.n3; rw [N, x3_run]; hit PN.write; exact hJ
  case write =>
    pnode x4 x4_ok write PN.write; rw [N, x4_run]; hit PN.sys
    refine ⟨hJ, ?_⟩
    simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne]
  case n5 =>
    pnode x5 x5_ok n5 PN.n5; rw [N, x5_run]
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
  case n6 => pnode x6 x6_ok n6 PN.n6; rw [N, x6_run]; hit PN.chk2; exact hJ
  case chk2 =>
    pnode x7 x7_ok chk2 PN.chk2; rw [N, x7_run]
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
  case n8 => pnode x8 x8_ok n8 PN.n8; rw [N, x8_run]; hit PN.chk3; exact hJ
  case chk3 =>
    pnode x9 x9_ok chk3 PN.chk3; rw [N, x9_run]
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
  case n10 => pnode x10 x10_ok n10 PN.n10; rw [N, x10_run]; hit PN.adv; exact hJ
  case adv =>
    pnode x11 x11_ok adv PN.adv; rw [N, x11_run]; hit PN.loop
    obtain ⟨k, ⟨h0, h8, h16, h24, hk⟩, hr0, hle, hP⟩ := hJ
    refine ⟨k + (σ.slot (-24)).toNat, ⟨?_, ?_, ?_, ?_, by omega⟩, hP⟩
    · simp [Spike.Lib.upd_apply, h0]
    · simp [Spike.Lib.upd_apply, h8]
    · simp only [Spike.Lib.upd_apply]; simp only [show (-8 : Int) ≠ -16 by decide, ite_true, ite_false]
      rw [h16, BitVec.add_comm, adv_buf]
    · simp only [Spike.Lib.upd_apply, ite_true]; rw [h24, adv_len hl64 hle]
  case fail =>
    pnode x12 x12_ok fail PN.fail; rw [N, x12_run]; exit PX.abort
    exact ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne], hJ⟩
  case done =>
    pnode x13 x13_ok done PN.done; rw [N, x13_run]; exit PX.ret
    · rw [hJ.2.1]
    · exact ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, hJ.1], hJ.2.2⟩

/-- **`hsvc_of_emitT` off the transfer sites**: the `write` system call's
node inside `NNZP SysW1` (`%rax = 1`, `%rdi = 1` decode to a `write` to fd 1;
`nodeW_nnzPSvcA`), `Z` at it (`hZ`). -/
theorem hsvc_of_emitTNN (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).pc
        [(.instr (.regular .W64 .W64 .syscall), 2)])
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c,
      At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → ms.bo s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c,
      At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp) s c →
      ∀ k c1, Q k c1 → ms.we s c1)
    (hZ : NodeW Z (fun _ _ => False) exe endPc R F
      ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp)) :
    SegTC (NNZP SysW1 exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5).withTp tp)) := by
  refine step_ndNNP (nodeW_nnzPSvcA (fun s he hn => hcode s he hn) ?_ hZ) fun s c hAt => ?_
  · rintro σ c ⟨⟨-, hdi, hax, -, -⟩, -⟩ call hd
    have hax' : σ.regs.rax.toNat = 1 := by
      simp only [Reg64s.get64] at hax; rw [UInt64.toNat, hax]; rfl
    have hdi' : σ.regs.rdi.toNat = 1 := by
      simp only [Reg64s.get64] at hdi; rw [UInt64.toNat, hdi]; rfl
    simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, hax', hdi'] at hd
    exact ⟨_, _, hd.symm⟩
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨⟨k, hL, hk, hP⟩, hdi, hax, hsi, hdx⟩, htp⟩ := id hAt
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
  refine Out.toT (.emit Scc.Sem.X64.abi _ _ (fun j c1 => P (k + j) c1) (Q k) hK
    (Scc.Sem.X64.atSyscall_of_cellAt hc) hd ⟨c, .refl c, hP⟩
    (fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h)
    (fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩) (fun c1 h => hwe s c hAt k c1 h))
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
      rfl
    rw [hs1]
    refine ⟨he, hn, hdc, ?_, syscallStep pc' r σ, hA', hD', ⟨k, ⟨h0, h8, h16, h24, hkl⟩, ?_⟩, ?_⟩
    · show pc' = _
      simp only [pc', N, ND.withTp, pcSys, Int64.add_assoc]; rfl
    · have hx0 : (syscallStep pc' r σ).regs.get64 .rax = r := by
        simp [syscallStep, syscallRegs, Reg64s.get64]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
    · simp only [syscallStep, syscallRegs]; exact htp
  · subst hj0; exact hPQ k c1 hPj

end ProofNN

end Spike.Lib.X64.Flow.Worker.PrintF.FA

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.FA.blkN_sys' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.FA.blkN_sys

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.FA.seg_printFANN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.FA.seg_printFANN

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.FA.hsvc_of_emitTNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.FA.hsvc_of_emitTNN
