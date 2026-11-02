/-
**`scc_rt_print` of a spawning program on x86-64, with the thread rows**
(the twin of `Spike/Lib/A64PrintF.lean`): `hello.w`'s `scc_rt_print`
(`Spike/Lib/X64HelloCode.lean`) is `hello1.w`'s
(`Spike/Lib/X64Print.lean`, `Spike/Lib/X64PrintA.lean`) block for block,
so the nodes, the exits and the code are `Print.PN`, `PrintA.N`,
`PrintA.E` and `Print.Code`; here they are taken with the thread pointer
(`ND.withTp`, the `%fs` base) and over `SegT`.

- `PrintF.lands_withTp`: landing at nodes with the thread pointer.
- `PrintF.FA.seg_printFA`: the function as one `SegT` segment against a
  source that prints byte by byte, from its entry to its return or its
  abort, the `write` system call (`.sys` to `.n5`) a given segment.
- `PrintF.FA.hsvc_of_emitT`: that system call from the output row
  (`Out.emit`, the memory side's byte step `ms.bo` and abort justification
  `ms.we`).
- `PrintF.cN`, `PrintF.cNe`, `PrintF.printF_callT`: a call of it from any
  call node (`call_ndT`).

The regions: inside the function the region is `[-40, 16)` from the
callee's base (`R.lo ≤ -40`, `16 ≤ R.hi`), `%rsp` at offset 8 on entry (the
return address at `[8, 16)`); a call node's offset `nC.o.sp` is the cell of
the pushed return address, the callee's base `nC.o.sp - 8`.

## Differences from the AArch64 version

- x86-64's `scc_rt_print` has no fence (TSO): there is no `.fence` node, no
  `PrintF.PN`/`PrintF.N`/`PrintF.pcSvc` of its own and no `bF`; the nodes
  are `Print.PN`'s, the system call node is `.sys` (A64 `.svc`).
- The code is `Print.Code` (`X64HelloWorker.printCode`), the entry fact is
  `.Lscc_rt_print.entry = scc_rt_print + 16` (`X64HelloWorker.printEntry`);
  there is no alignment premise (`hal`).
- The call's return address is the word the `call` pushed (the caller's
  cell at `nC.o.sp`, as `X64PrintCall.PrintCall.pN`) for A64's `x30`; the
  return restores `%rbp` (A64: `x29`, `x30`) and lands past the popped
  return address (`nC.o.sp + 8`).
- A64's `seg_printF` (the stand-still source) is not twinned: hello's
  consumers use the byte-by-byte one, and the stand-still function is
  `Print.seg_printW`.
-/
import Spike.Lib.X64WorkerRows
import Spike.Lib.X64PrintCall
import Spike.Lib.LowerX64.NodeTp

set_option linter.unusedSimpArgs false

namespace Spike.Lib.X64.Flow.Worker.PrintF

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow

/-- The code does not depend on the ghosts (the nodes' pcs do not). -/
theorem codeG {exe : _root_.Executable} {endPc : Int64} {c0 c0' : Ctl} {rbp0 ra rbp0' ra' : BitVec 64}
    (h : Print.Code c0 rbp0 ra exe endPc) : Print.Code c0' rbp0' ra' exe endPc :=
  ⟨h.e, h.n1, h.loop, h.n3, h.write, h.n5, h.n6, h.chk2, h.n8, h.chk3, h.n10, h.adv, h.fail, h.done, h.sys⟩

/-- Landing at nodes with the thread pointer `tp` (`ND.withTp`): landing
at the nodes, the `%fs` base holding `tp`. -/
theorem lands_withTp {ι κ : Sort _} {N : ι → ND} {E : κ → ND} {am : AM} {c : Ctl} {tp : UInt64}
    (ht : am.σ.regs.fsBase = tp) (h : Lands N E am c) :
    Lands (fun j => (N j).withTp tp) (fun x => (E x).withTp tp) am c := by
  rcases h with ⟨j, a, b, d⟩ | ⟨x, a, b, d⟩
  · exact .inl ⟨j, a, b, d, ht⟩
  · exact .inr ⟨x, a, b, d, ht⟩

namespace FA

open Spike.Lib.X64.Print (PN PX x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI oE pcSys
  x0_ok x1_ok x2_ok x3_ok x4_ok x5_ok x6_ok x7_ok x8_ok x9_ok x10_ok x11_ok x12_ok x13_ok
  x0_run x1_run x2_run x3_run x4_run x5_run x6_run x7_run x8_run x9_run x10_run x11_run x12_run x13_run)
open Spike.Lib.X64.PrintA (N E JL JI JIlt RC0 RC1 RC2 C4 C11 len_zero sub_z pos_not_le refused_le refused_ne4
  refused_ne11 adv_buf adv_len rc0_of_retOk)

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop} {tp : UInt64}

set_option hygiene false in
/-- A block node with the thread pointer: the block, its `okBlk`, its code;
the source stays, the block keeps the `%fs` base (`arun_fsBase`); the edge
(without the thread pointer) is left, the invariant in `hJ`. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| (refine Seg.toT (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJt => ⟨c, .refl c,
      lands_withTp (by rw [arun_fsBase]; exact hJt.2) ?_⟩); have hJ := hJt.1; dsimp only [ND.withTp]))

set_option hygiene false in
/-- Hitting node `j`: the pc and offsets; the invariant is left, unfolded. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> try simp only [N]) <;>
    try first | rfl | exact hentry | (simp only [Int64.add_assoc]; rfl))

/-- Hitting exit `x`: the offsets; the pc and the invariant are left. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> try simp only [E]) <;> try rfl)

set_option maxHeartbeats 1000000 in
/-- **Hello's `scc_rt_print` is one segment with the thread rows** against
a source that prints byte by byte (`PrintA.seg_printAW` over `SegT`, the
nodes with the thread pointer `tp`): the block nodes keep the source where
it is, the system call (`hsvc`, a given segment from `.sys` to `.n5`) moves
it by the count it returns. The code is `Print.Code` (any `c0`); the region
is `[-40, 16)`. -/
theorem seg_printFA (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hlen : len0 < 2 ^ 63) (hcode : Print.Code c0 rbp0 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hsvc : SegT p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5).withTp tp))) :
    SegT p lbl ms (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .e).withTp tp))
      (fun s c => ∃ x, At exe endPc R F
        ((E (_root_.Executable.labels exe).label rbp0 ra len0 P Q x).withTp tp) s c) := by
  have hl64 : len0 < 2 ^ 64 := by omega
  refine fn_segT (N := fun i => (N _ rbp0 ra buf0 len0 P Q i).withTp tp)
    (E := fun x => (E _ rbp0 ra len0 P Q x).withTp tp) (fun i => ?_) PN.e
  cases i
  case sys => exact hsvc.mono_post fun _ _ h => .inl ⟨PN.n5, h⟩
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

/-- **The write system call from the output row** (`PrintA.hsys_of_emit`
over `SegT` with the thread pointer, the row `Out.emit` with the memory
side's byte step `ms.bo` and abort justification `ms.we`): from `.sys` to
`.n5`. The `syscall` keeps the `%fs` base. -/
theorem hsvc_of_emitT (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
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
      ∀ k c1, Q k c1 → ms.we s c1) :
    SegT p lbl ms (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .n5).withTp tp)) := by
  refine SegT.step fun s c hAt => ?_
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

end Proof

end FA

/-! ## The call -/

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _}
  {N' : ι → ND} {E' : κ → ND}

/-- The callee's nodes for the call state `σC` at a call node of offset
`ko` (the pushed return address in the caller's cell `ko`): `%rbp`, the
return address, the buffer `%rdi` and the count `%rsi` of `σC`, the source
predicates `Pc σC`, `Qc σC`, the thread pointer `σC`'s `%fs` base. -/
abbrev cN (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) (i : Print.PN) : ND :=
  (PrintA.N lab σC.regs.rbp.toBitVec (σC.slot ko) (σC.regs.get64 .rdi) (σC.regs.get64 .rsi).toNat (Pc σC) (Qc σC)
    i).withTp σC.regs.fsBase

/-- The callee's exits for the call state `σC`. -/
abbrev cE (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) (x : Print.PX) : ND :=
  (PrintA.E lab σC.regs.rbp.toBitVec (σC.slot ko) (σC.regs.get64 .rsi).toNat (Pc σC) (Qc σC) x).withTp
    σC.regs.fsBase

/-- The callee's entry, pinned to the call state `σC` entered at `nC`'s
offset less the pushed return address, a realizable one. -/
def cNe (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (nC : ND) (σC : AS) : ND :=
  ⟨(cN lab Pc Qc nC.o.sp σC .e).pc, (cN lab Pc Qc nC.o.sp σC .e).o, fun σ c =>
    (cN lab Pc Qc nC.o.sp σC .e).J σ c ∧ σ = enter (nC.o.sp - 8) σC ∧ ∃ c0, nC.J σC c0⟩

/-- **A call of hello's `scc_rt_print` with the thread rows**, from any
call node `nC` (pc `scc_rt_print`, the pushed return address at offset
`nC.o.sp`, print's region `[-40, 16)` from `nC.o.sp - 8` inside `R`):
`call_ndT` with `seg_printFA`, for any source predicates `Pc`/`Qc` of the
call state. The write system call (`hsvc`) is asked in every callee region
and frame condition, at every call state (`hsvc_of_emitT` gives it from the
output row); the return (`hret`, `%rbp` and the `%fs` base restored, past
the popped return address) and the abort (`habort`) land at the caller's
nodes. -/
theorem printF_callT {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    {c0' : Ctl} {rbp' ra' : BitVec 64} (hcode : Print.Code c0' rbp' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pc σ 0 c)
    (hlen : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat < 2 ^ 63)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -40 → 16 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ σC c, nC.J σC c →
      SegT p lbl ms (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC .sys))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC .n5)))
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      σR.regs.fsBase = σC.regs.fsBase → Pc σC (σC.regs.get64 .rsi).toNat c' →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - 8) (-40) 16).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N' E' ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 → Qc σC k c' →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - 8) (-40) 16).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N' E' ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F nC) (Next exe endPc R F N' E') := by
  refine call_ndT (e0 := 8) (lo' := -40) (hi' := 16) (Ne := cNe (_root_.Executable.labels exe).label Pc Qc nC)
    (Ex := cE (_root_.Executable.labels exe).label Pc Qc nC.o.sp)
    hR hF hlo (by decide) (by omega) hhi hk8 (by decide) (by decide)
    (fun R' F' hR' hlo' hhi' hF' hFF σC => ?_) (fun _ => rfl) ?_ ?_
  · by_cases hg : ∃ c0, nC.J σC c0
    · obtain ⟨c0, hJ0⟩ := hg
      refine (FA.seg_printFA hF' hR' hlo' hhi' (hlen σC c0 hJ0) (c0 := c0) (tp := σC.regs.fsBase)
        (codeG hcode) hentry (hsvc R' F' hR' hlo' hhi' hF' hFF σC c0 hJ0)).mono_pre ?_
      rintro s c ⟨a, b, d, e, σ, hA, hD, hJ', -, -⟩
      exact ⟨a, b, d, e, σ, hA, hD, hJ'⟩
    · exact SegT.step fun s c ⟨_, _, _, _, _, _, _, _, _, h⟩ => absurd h hg
  · intro σC c hJ
    exact ⟨σC, hpc.symm, ⟨⟨hP0 σC c hJ, rfl, by simp [enter], rfl, by simp [enter]⟩, rfl⟩, rfl, c, hJ⟩
  · rintro g y σC c σx c' σR hJ ⟨-, he, -⟩ hx hreg - - hsl
    obtain rfl : σC = g := enter_inj he
    cases y
    · obtain ⟨⟨hbp, hP⟩, htp⟩ := hx
      have h := hret σC c σR c' hJ (by rw [hreg]; exact hbp) (by rw [hreg]; exact htp) hP hsl
      have e : nC.o.sp - 8 + 16 = nC.o.sp + 8 := by omega
      simp only [cE, PrintA.E, ND.withTp]
      rw [e]
      exact h
    · obtain ⟨⟨h4, k, hQ⟩, -⟩ := hx
      exact habort σC c σR c' k hJ (by rw [hreg]; exact h4) hQ hsl

end Call

end Spike.Lib.X64.Flow.Worker.PrintF

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.FA.seg_printFA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.FA.seg_printFA

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.FA.hsvc_of_emitT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.FA.hsvc_of_emitT

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.printF_callT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.printF_callT
