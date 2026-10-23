/-
**The abort stubs on x64 inside `W`**: `seg_stub` (`Spike/Lib/X64Abort.lean`)
with every state of the stub in a predicate `W` and moved by no outside move
`K`, under any frame condition `F` stable in the stub's region (a callee's,
`call_nd_FW`), for the consumers' per-state facts (`SFacts`,
`Spike/Lib/X64SegInst.lean`) on the overflow abort path. The AArch64 mirror is
`Spike/Lib/A64AbortW.lean`.

* `seg_stubW`: a stub from its entry is a `SegW` to any fragment, given its
  argument block `x1`, the `write` call's segment inside `W` (`hsys`), the
  states of every node inside `W` (`NodeW`, `BlkW`) and the exit call at an
  abort site (`hab`);
* `seg_overflowW`: `scc_rt_abort_overflow`;
* `BlkW.mono_F`, `NodeW.mono_At`: a node's states lifted into a larger
  predicate under the frame condition (the stub's `SFacts`, with places from `F`);
* `Disp.DN.nd1`, `Disp.seg_disp1W`: the dispatcher `scc_rt_abort` at the
  overflow code `1` (only the first test taken, every other node dead), to
  the overflow stub's entry; `Disp.seg_abort1W`: composed with the stub;
* `Local.seg_localW`: a function's `.ovf` block (`movl $1, %edi; call
  scc_rt_abort`, `Local.lb`; the `ud2` after it is dead) in its frame, then
  `scc_rt_abort(1)` (`call_nd_FW`, the callee's region `[-24, 16)` from its
  frame base inside the function's region), given the abort path's
  obligations per callee region and source control (`Local.StubW`);
  `Local.seg_localW_adv`: the same with the source advanced by a local run
  at the call; `Local.at_lag`, `Local.seg_localW_lag`: from the block held
  back (`Lag`, after `SegW.lag`), the source released to the real control
  at the call.
-/
import Spike.Lib.X64Abort
import Spike.Lib.X64Call
import Spike.Lib.SegLag

namespace Spike.Lib.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64 Spike.Lib.X64

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **An abort stub inside `W` does not return**: `seg_stub` with every
node's states in `W`, moved by no `K` (`hWe` … `hWex`: the prologue `x0`,
the `leaq`, the argument block `x1`, the tail `x2`, the exit call), the
`write` call a segment inside `W` (`hsys`). -/
theorem seg_stubW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} (st : Stub)
    {x1 : List (Directive × Nat)} (hne1 : x1 ≠ [])
    (hok1 : okBlk (-24) 16 oI x1 = true)
    (h1 : ∀ σ c, JI c0 σ c → Hit (N (_root_.Executable.labels exe).label st c0 .sys)
      (arun (_root_.Executable.labels exe).label x1
        ⟨(N (_root_.Executable.labels exe).label st c0 .n2).pc, oI, σ⟩) c)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code st c0 x1 exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label st c0 .e) x0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label st c0 .n1))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label st c0 .n2) x1)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label st c0 .n5) x2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label st c0 .ex))
    (hsys : SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label st c0 .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label st c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label st c0 .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label st c0 .e)) Q := by
  refine (fn_segW (N := N _ st c0) (E := E) (fun i => ?_) PN.e).mono_post fun _ _ ⟨x, _⟩ => nomatch x
  have hentry := hcode.hentry
  have hexit := hcode.hexit
  cases i
  case e =>
    refine seg_ndW (by simp [x0]) x0_ok hF hR hlo hhi (fun s he hn => hcode.e s he hn) hWe
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [N, x0_run]; hit PN.n1
  case n1 =>
    refine si_ndW (si := siMsg st) rfl hF (fun s he hn => hcode.n1 s he hn) hWn1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    hit PN.n2
  case n2 =>
    exact seg_ndW hne1 hok1 hF hR hlo hhi (fun s he hn => hcode.n2 s he hn) hWn2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.sys, h1 σ c hJ⟩⟩
  case sys => exact seg_givenW PN.n5 hsys
  case n5 =>
    refine seg_ndW (by simp [x2]) x2_ok hF hR hlo hhi (fun s he hn => hcode.n5 s he hn) hWn5
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [N, x2_run]; hit PN.ex
  case ex =>
    refine exit_ndW hK (fun s he hn => hcode.ex s he hn) hWex (fun σ c hJ => ?_)
      fun s c _ hAt _ _ => SysOk.exitGroup_abort (hab s c hAt)
    have h := hJ.2.1
    simp only [Reg64s.get64] at h
    show σ.regs.rax.toBitVec.toNat = 231
    rw [h]; rfl

end Proof

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isa}

/-- **`scc_rt_abort_overflow` inside `W` does not return.** -/
theorem seg_overflowW {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code overflow c0 x1Overflow exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .e) x0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .n1))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .n2) x1Overflow)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .n5) x2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .ex))
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label overflow c0 .e)) Q :=
  seg_stubW overflow (by simp [x1Overflow]) x1Overflow_ok (by arg_hit x1Overflow_run)
    hF hR hlo hhi hcode hK hWe hWn1 hWn2 hWn5 hWex hsys hab

end Stubs

/-! ## Lifting a node's states into a larger predicate -/

section Lift

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A block node's states in a larger predicate**: `BlkW W` gives
`BlkW W'` when every state inside the block (its memory under `F`, which no
write inside `R` breaks) of a source control of the node's invariant in `W`
is in `W'` (as for the stub's `SFacts`, whose places come from `F`). -/
theorem _root_.Spike.Lib.X64.BlkW.mono_F {W W' : Frag isa} {K : State → State → Prop}
    {n : ND} {blk : List (Directive × Nat)}
    (hF : FStable R F) (h : BlkW W K exe endPc R F n blk)
    (himp : ∀ s c σ, n.J σ c → F s.st.1 → W s c → W' s c) : BlkW W' K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hDF =>
    have ⟨hw, hK⟩ := h s σ c he hn hd hpc hA hD hJ k hk m hA' hDF
    ⟨himp _ c σ hJ (hF _ _ hD hDF) hw, hK⟩

/-- **A node's states in a larger predicate.** -/
theorem _root_.Spike.Lib.X64.NodeW.mono_At {W W' : Frag isa} {K : State → State → Prop} {n : ND}
    (h : NodeW W K exe endPc R F n) (himp : ∀ s c, At exe endPc R F n s c → W s c → W' s c) :
    NodeW W' K exe endPc R F n :=
  fun s c hA => have ⟨hw, hK⟩ := h s c hA; ⟨himp s c hA hw, hK⟩

end Lift

/-! ## The dispatcher at the overflow code -/

namespace Disp

/-! `scc_rt_abort(1)`: with the code `1` only the first test is taken; every
other node is dead (`DN.nd1`), and the one exit reached is the overflow
stub's entry. -/

section Spec

variable (lab : Label → Int64) (c0 : Ctl)

/-- **The nodes at the overflow code**: the entry with `%rdi = 1`, the first
test with `1` stored, its taken jump; every other node dead. -/
def DN.nd1 : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 1#64⟩
  | .t1 => ⟨lab ".Lscc_rt_abort.entry", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 1#64⟩
  | .g1 => ⟨lab ".Lscc_rt_abort.is0", oD, fun _ c => c = c0⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

/-- The code of `DN.nd1`'s nodes is `DN.nd`'s: the same pcs. -/
theorem DN.nd1_pc (i : DN) : (DN.nd1 lab c0 i).pc = (DN.nd lab c0 i).pc := by
  cases i <;> rfl

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **`scc_rt_abort(1)` inside `W` is one segment** from its entry to the
overflow stub's entry, given the states of the entry block, the first test
and its taken jump inside `W` (`hWe`, `hWt1`, `hWg1`). -/
theorem seg_disp1W {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .t1) t1)
    (hWg1 : BlkW W K exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .g1) g1) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .e))
      (At exe endPc R F (DX.nd (_root_.Executable.labels exe).label c0 .overflow)) := by
  refine (fn_segW (N := DN.nd1 (_root_.Executable.labels exe).label c0)
    (E := fun (_ : Unit) => DX.nd (_root_.Executable.labels exe).label c0 .overflow) (fun i => ?_)
    DN.e).mono_post fun _ _ ⟨_, h⟩ => h
  have hentry := hcode.hentry
  cases i
  case e =>
    refine seg_ndW (by simp [d0]) d0_ok hF hR (by omega) hhi (fun s he hn => hcode.e s he hn) hWe
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd1, d0_run]
    refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;>
      simp_all [DN.nd1, upd_apply]
  case t1 =>
    refine seg_ndW (by simp [t1]) t1_ok hF hR (by omega) hhi (fun s he hn => hcode.t1 s he hn) hWt1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd1, t1_run]
    split
    · refine .inl ⟨DN.g1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd1]
    · next h => exact absurd (by rw [hJ.2]; decide) h
  case g1 =>
    refine seg_ndW (by simp [g1]) g1_ok hF hR (by omega) hhi (fun s he hn => hcode.g1 s he hn) hWg1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd1, g1_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;> simp_all [DN.nd1, DX.nd, DX.stub, Abort.N, Abort.overflow]
  all_goals exact dead_ndW fun _ _ h => h

/-- **`scc_rt_abort(1)` inside `W` does not return**: the dispatcher at the
overflow code (`seg_disp1W`) then `scc_rt_abort_overflow` (`seg_overflowW`);
the stub's frame base is the dispatcher's (`DX.nd .overflow` is the stub's
entry node). -/
theorem seg_abort1W {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .t1) t1)
    (hWg1 : BlkW W K exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .g1) g1)
    (hK : ms.K = some Scc.Sem.X64.abi) (hcs : Abort.Code overflow c0 x1Overflow exe endPc)
    (hSe : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .e) x0)
    (hSn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n1))
    (hSn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n2)
      x1Overflow)
    (hSn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n5) x2)
    (hSex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .ex))
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .sys))
      (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd1 (_root_.Executable.labels exe).label c0 .e)) Q :=
  (seg_disp1W hF hR hlo hhi hcode hWe hWt1 hWg1).seq
    (seg_overflowW hF hR hlo hhi hcs hK hSe hSn1 hSn2 hSn5 hSex hsys hab)

end Proof

end Disp

/-! ## The function-local abort block -/

namespace Local

/-! A function's `.ovf` block: `movl $1, %edi; call scc_rt_abort` (then a
dead `ud2`), at static offsets `o` in the function's frame. The call does
not return. -/

/-- The block (without the dead `ud2`). -/
def lb : List (Directive × Nat) := (parse("movl $1, %edi
call scc_rt_abort")).zip [5, 5]

theorem lb_ok (o : SO) (h8 : o.sp % 8 = 0) : okBlk (o.sp - 8) o.sp o lb = true := by
  simp [lb, okBlk, classify, AI.ok, AI.isTerm, RegOnly, soReg, regDst, SO.write, offOk, AI.so, Reg.base, SO.kill]
  omega

/-- **The block's run**: at `scc_rt_abort` with `%rdi = 1`, the return
address pushed, every other cell unchanged. -/
theorem lb_run (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) :
    (arun lab lb ⟨pc, o, σ⟩).pc = lab "scc_rt_abort" ∧ (arun lab lb ⟨pc, o, σ⟩).σ.regs.get64 .rdi = 1#64 ∧
      (arun lab lb ⟨pc, o, σ⟩).so.sp = o.sp - 8 ∧
      ∀ k, k ≠ o.sp - 8 → (arun lab lb ⟨pc, o, σ⟩).σ.slot k = σ.slot k := by
  simp [lb, arun, dstep, classify, AI.tgt, AI.so, AI.step, RegOnly, regRes, soReg, regDst, Reg.base, SO.kill,
    SO.write, Operation.interp, Operand.interp, MachineData.set, MachineData.setReg, Reg64s.set,
    ConstExpr.interp, Reg64s.get64, upd_apply]
  intro k hk h; exact absurd h hk

/-- **The abort path's obligations for one source control `c0`** in the
callee's region `R` and frame condition `F`: the dispatcher's and the
overflow stub's code, their nodes' states inside `W` (moved by no `K`), the
stub's `write` call a segment inside `W`, and its exit call at an abort
site. -/
structure StubW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) : Prop where
  dcode : Disp.Code c0 exe endPc
  de : BlkW W K exe endPc R F (Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .e) Disp.d0
  dt1 : BlkW W K exe endPc R F (Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .t1) Disp.t1
  dg1 : BlkW W K exe endPc R F (Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .g1) Disp.g1
  scode : Abort.Code overflow c0 x1Overflow exe endPc
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .e) x0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n1)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n2) x1Overflow
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n5) x2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .ex)
  sys : SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .sys))
    (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .n5))
  ab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label overflow c0 .ex) s c → ms.abortAt s

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- The nodes: the block (`false`, at offsets `o`) and the call's landing at
`scc_rt_abort` (`true`, the return address pushed), with the source and the
cells but the return address's as at the block and `%rdi = 1`. -/
def LN (lab : Label → Int64) (o : SO) (pcA : Int64) (JA : AS → Ctl → Prop) : Bool → ND
  | false => ⟨pcA, o, JA⟩
  | true => ⟨lab "scc_rt_abort", ⟨o.sp - 8, []⟩, fun σ c =>
      (∃ σ0, JA σ0 c ∧ ∀ k, k ≠ o.sp - 8 → σ.slot k = σ0.slot k) ∧ σ.regs.get64 .rdi = 1#64⟩

/-- **A function's `.ovf` block inside `W` does not return**: from the
block (at `pcA`, static offsets `o` in the function's region `R`, invariant
`JA`) it is a segment to any fragment, given the block's states inside `W`
(`hW`) and, for the callee's region and frame condition at the call and the
source control `c0` of a state of `JA`, the abort path's obligations
(`hstub`, `StubW`). The callee's region (`[-24, 16)` from its frame base
`o.sp - 16`) is inside `R` (`hlo`, `hhi`). `hstub` may use that every
memory of the callee's frame condition holds the caller's cells outside the
callee's region as at the call, where the cells but the return address's are
those of a state of `JA` (the source of the abort's places). -/
theorem seg_localW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} {o : SO} {pcA : Int64}
    {JA : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ o.sp - 40) (hhi : o.sp ≤ R.hi) (h8 : o.sp % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcA lb)
    (hW : BlkW W K exe endPc R F (LN (_root_.Executable.labels exe).label o pcA JA false) lb)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k →
      ¬ (R.callee (o.sp - 8 - 8) (-24) 16).Off (k - (o.sp - 8 - 8)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -24 → 16 ≤ R'.hi → FStable R' F' →
      KStable K F' → (∀ m, F' m → F m) → R' = R.callee (o.sp - 8 - 8) (-24) 16 →
      ∀ c0, (∃ σ0, JA σ0 c0) →
      (∀ m, F' m → ∃ mC σC σ0, Abs R ⟨o.sp - 8, []⟩ mC σC ∧ (∀ k, k ≠ o.sp - 8 → σC.slot k = σ0.slot k) ∧
        JA σ0 c0 ∧ ∀ k, R.Off k → ¬ R'.Off (k - (o.sp - 8 - 8)) →
          Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubW W K p lbl ms exe endPc R' F' c0) :
    SegW W K p lbl ms (At exe endPc R F (LN (_root_.Executable.labels exe).label o pcA JA false)) Q := by
  refine (fn_segW (N := LN (_root_.Executable.labels exe).label o pcA JA) (E := fun x : Empty => nomatch x)
    (fun i => ?_) false).mono_post fun _ _ ⟨x, _⟩ => nomatch x
  cases i
  case false =>
    refine seg_ndW (by simp [lb]) (lb_ok o h8) hF hR (by omega) hhi hcode hW fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := lb_run (_root_.Executable.labels exe).label pcA o σ
    refine .inl ⟨true, h1.symm, ?_, ⟨σ, hJ, h4⟩, h2⟩
    simp only [LN] at h3 ⊢; simp [SO.le, h3]
  case true =>
    refine call_nd_FW (e0 := 8) (lo' := -24) (hi' := 16) (M := fun _ => True)
      (Ne := fun g => Disp.DN.nd1 (_root_.Executable.labels exe).label g .e) (Ex := fun _ (x : Empty) => nomatch x)
      hR hF (by show R.lo ≤ o.sp - 8 - 8 + -24; omega) (by decide) (by show o.sp - 8 - 8 < R.hi; omega)
      (by show o.sp - 8 - 8 + 16 ≤ R.hi; omega) (by show (o.sp - 8 - 8) % 8 = 0; omega) (by decide) (by decide)
      hFK hKR (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g hg hcc => ?_) (fun _ => rfl) ?_ ?_
    · obtain ⟨σC, c, ⟨⟨σ0, hJA, -⟩, -⟩, ⟨rfl, -⟩⟩ := hg
      have hs := hstub R' F' hR' hlo' hhi' hF' hK' hFF' hR'e c ⟨σ0, hJA⟩ fun m hm => by
        obtain ⟨mC, σC', c', hA, ⟨⟨σ0', hJA', hsl⟩, -⟩, ⟨rfl, -⟩, hk⟩ := hcc m hm
        exact ⟨mC, σC', σ0', hA, hsl, hJA', hk⟩
      exact Disp.seg_abort1W hF' hR' hlo' hhi' hs.dcode hs.de hs.dt1 hs.dg1 hK hs.scode hs.se hs.sn1
        hs.sn2 hs.sn5 hs.sex hs.sys hs.ab
    · rintro σC c ⟨-, hx⟩
      exact ⟨c, rfl, rfl, by simpa [enter] using hx⟩
    · intro _ x
      exact nomatch x

/-- **A node held back is a node at the held-back invariant**: `Lag` of
`At` at `n` is `At` at `n` with `LagJ` for `n.J`. -/
theorem at_lag {C : Ctl → Prop} {n : ND} {s : State} {c : Ctl}
    (h : Lag p C (At exe endPc R F n) s c) : At exe endPc R F ⟨n.pc, n.o, LagJ p C n.J⟩ s c := by
  obtain ⟨c', ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩, hr, hc⟩ := h
  exact ⟨h1, h2, h3, h4, σ, hA, hF, c', hJ, hr, hc⟩

/-- The nodes of the block releasing a held-back source: the block at `JA`
(`false`) and the call's landing at `scc_rt_abort` (`true`) at `JB`, the
source advanced by a local run (`seg_localW_adv`). -/
def LNa (lab : Label → Int64) (o : SO) (pcA : Int64) (JA JB : AS → Ctl → Prop) : Bool → ND
  | false => ⟨pcA, o, JA⟩
  | true => ⟨lab "scc_rt_abort", ⟨o.sp - 8, []⟩, fun σ c =>
      (∃ σ0, JB σ0 c ∧ ∀ k, k ≠ o.sp - 8 → σ.slot k = σ0.slot k) ∧ σ.regs.get64 .rdi = 1#64⟩

/-- **A function's `.ovf` block, the source advanced at the call**
(`seg_localW` with the block's invariant `JA` and the abort path's `JB`):
every control of `JA` reaches one of `JB` at the same state by a local run
(`hadv`), taken at the block's exit, and the abort path's obligations are
asked at `JB`'s controls. The callee is not promised that outside moves
keep its frame condition (`call_nd_FWK` at `KC := False`), so nothing is
asked of `K` and `F`. -/
theorem seg_localW_adv {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} {o : SO} {pcA : Int64}
    {JA JB : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ o.sp - 40) (hhi : o.sp ≤ R.hi) (h8 : o.sp % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcA lb)
    (hW : BlkW W K exe endPc R F (LNa (_root_.Executable.labels exe).label o pcA JA JB false) lb)
    (hadv : ∀ σ c, JA σ c → ∃ c', LocalRun p c c' ∧ JB σ c')
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -24 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → R' = R.callee (o.sp - 8 - 8) (-24) 16 →
      ∀ c0, (∃ σ0, JB σ0 c0) →
      (∀ m, F' m → ∃ mC σC σ0, Abs R ⟨o.sp - 8, []⟩ mC σC ∧ (∀ k, k ≠ o.sp - 8 → σC.slot k = σ0.slot k) ∧
        JB σ0 c0 ∧ ∀ k, R.Off k → ¬ R'.Off (k - (o.sp - 8 - 8)) →
          Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubW W K p lbl ms exe endPc R' F' c0) :
    SegW W K p lbl ms (At exe endPc R F (LNa (_root_.Executable.labels exe).label o pcA JA JB false)) Q := by
  refine (fn_segW (N := LNa (_root_.Executable.labels exe).label o pcA JA JB) (E := fun x : Empty => nomatch x)
    (fun i => ?_) false).mono_post fun _ _ ⟨x, _⟩ => nomatch x
  cases i
  case false =>
    refine seg_ndW (by simp [lb]) (lb_ok o h8) hF hR (by omega) hhi hcode hW fun σ c hJ => ?_
    obtain ⟨c', hr, hJB⟩ := hadv σ c hJ
    refine ⟨c', hr, ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := lb_run (_root_.Executable.labels exe).label pcA o σ
    refine .inl ⟨true, h1.symm, ?_, ⟨σ, hJB, h4⟩, h2⟩
    simp only [LNa] at h3 ⊢; simp [SO.le, h3]
  case true =>
    refine call_nd_FWK (KC := False) (e0 := 8) (lo' := -24) (hi' := 16) (M := fun _ => True)
      (Ne := fun g => Disp.DN.nd1 (_root_.Executable.labels exe).label g .e) (Ex := fun _ (x : Empty) => nomatch x)
      hR hF (by show R.lo ≤ o.sp - 8 - 8 + -24; omega) (by decide) (by show o.sp - 8 - 8 < R.hi; omega)
      (by show o.sp - 8 - 8 + 16 ≤ R.hi; omega) (by show (o.sp - 8 - 8) % 8 = 0; omega) (by decide) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF' hR'e _ g hg hcc => ?_) (fun _ => rfl) ?_ ?_
    · obtain ⟨σC, c, ⟨⟨σ0, hJB, -⟩, -⟩, ⟨rfl, -⟩⟩ := hg
      have hs := hstub R' F' hR' hlo' hhi' hF' hFF' hR'e c ⟨σ0, hJB⟩ fun m hm => by
        obtain ⟨mC, σC', c', hA, ⟨⟨σ0', hJB', hsl⟩, -⟩, ⟨rfl, -⟩, hk⟩ := hcc m hm
        exact ⟨mC, σC', σ0', hA, hsl, hJB', hk⟩
      exact Disp.seg_abort1W hF' hR' hlo' hhi' hs.dcode hs.de hs.dt1 hs.dg1 hK hs.scode hs.se hs.sn1
        hs.sn2 hs.sn5 hs.sex hs.sys hs.ab
    · rintro σC c ⟨-, hx⟩
      exact ⟨c, rfl, rfl, by simpa [enter] using hx⟩
    · intro _ x
      exact nomatch x

/-- **A function's `.ovf` block held back** (the post of a segment after
`SegW.lag`): from the block with its controls held back at those of `C`
(`Lag`), `seg_localW_adv` with `JA := LagJ p C J`, the source released to
`J`'s control at the call, the abort path's obligations at `J`'s controls
(`hstub`); the block's states at the held-back controls (`hW`). -/
theorem seg_localW_lag {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} {o : SO} {pcA : Int64}
    {C : Ctl → Prop} {J : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ o.sp - 40) (hhi : o.sp ≤ R.hi) (h8 : o.sp % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcA lb)
    (hW : BlkW W K exe endPc R F (LNa (_root_.Executable.labels exe).label o pcA (LagJ p C J) J false) lb)
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -24 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → R' = R.callee (o.sp - 8 - 8) (-24) 16 →
      ∀ c0, (∃ σ0, J σ0 c0) →
      (∀ m, F' m → ∃ mC σC σ0, Abs R ⟨o.sp - 8, []⟩ mC σC ∧ (∀ k, k ≠ o.sp - 8 → σC.slot k = σ0.slot k) ∧
        J σ0 c0 ∧ ∀ k, R.Off k → ¬ R'.Off (k - (o.sp - 8 - 8)) →
          Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubW W K p lbl ms exe endPc R' F' c0) :
    SegW W K p lbl ms (Lag p C (At exe endPc R F (LN (_root_.Executable.labels exe).label o pcA J false))) Q :=
  (seg_localW_adv hF hR hlo hhi h8 hK hcode hW (fun _ _ ⟨c', hJ, hr, _⟩ => ⟨c', hr, hJ⟩)
    hstub).mono_pre fun _ _ hl => at_lag hl

end Proof

end Local

end Spike.Lib.X64.Abort
