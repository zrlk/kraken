/-
**A call of `print` from any caller node** (x86-64): `callBlock`'s
`.print` case (`Scc/Lower/Term.lean`), its argument block
(`Spike/Lib/LowerX64/PrintArgs.lean`) around the multiply's flag node and
`call scc_rt_print`, composed with `print_call_segW`
(`Spike/Lib/X64PrintCall.lean`) at the call site; the twin of
`Spike/Lib/LowerA64/PrintCall.lean`.

- `callD`, `arun_callD`, `okBlk_callD`: the `call`'s directive, its run (to
  `print`'s label, the return address pushed below `%rsp`) and coverage;
  `okBlk_widen` (a covered block is covered in a wider region).
- `PBlk`: the block's cells (before the multiply, the multiply, after it,
  the `call`) and pcs; its states `PBlk.st1`, `PBlk.st3`, `PBlk.stC` and
  nodes `PBlk.n0`, `PBlk.nM`, `PBlk.n2`, `PBlk.n3`, `PBlk.nC` (the call
  node, `%rsp` at `-size - 8`).
- `print_blocks_segW`: for any such cells running through, the block,
  multiply, block, `call` and `print`'s run are one segment inside `W`
  (`seg_ndW`, `flag_ndW`, `seg_ndW`, `seg_ndW`, `print_call_segW`).
- `callBlock`'s `.print` case: `preD`, `postD`, `pblk`, `opdNat`;
  `stC_facts` (`%rdi`, `%rsi = min(n, 8·m)`, the return address and the
  cells kept at `print`'s entry), `opdVal_keptX`, `printN_of_rsi`; and
  `print_block_segW`, where `print_call_segW`'s count premise is discharged
  from the block.

Where x86-64 differs from AArch64: the multiply is a node of its own
(`mulFI`), and the `call` pushes the return address into the cell below the
frame, so the call node's offsets are `⟨-size - 8, []⟩` and the `call` cell
is its own block, covered in `[-size - 8, -size)`.
-/
import Spike.Lib.LowerX64.PrintArgs
import Spike.Lib.X64PrintCall

namespace Spike.Lib.LowerX64

open CoreLang
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item i64 i32 xr or_)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.X64.PrintCall (pN pR pF pcS)
open Spike.Lib.X64.PrintA (PrintAW EmitW)

set_option linter.unusedSimpArgs false

/-- `call scc_rt_print`'s directive. -/
def callD : Directive := i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.print))

theorem classify_callD : classify callD = some (.call "scc_rt_print") := rfl

/-- **`call scc_rt_print`'s run**: to `print`'s label, the return address
pushed below `%rsp`. -/
theorem arun_callD (lab : String → Int64) (o : SO) (pc : Int64) (σ : AS) (z : Nat) :
    arun lab [(callD, z)] ⟨pc, o, σ⟩ = ⟨lab "scc_rt_print", { o with sp := o.sp - 8 },
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64),
               slot := upd σ.slot (o.sp - 8) (pc + Int64.ofNat z).toBitVec }⟩ := by
  simp only [arun, List.foldl, dstep, classify_callD, AI.tgt, AI.so, AI.step]

theorem okBlk_callD {lo hi : Int} {o : SO} {z : Nat} (h : offOk lo hi (o.sp - 8) = true) :
    okBlk lo hi o [(callD, z)] = true := by
  simp [okBlk, classify_callD, AI.ok, h]

/-- **A covered block is covered in a wider region.** -/
theorem okBlk_widen {lo hi lo' hi' : Int} (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ {o : SO} {blk : List (Directive × Nat)}, okBlk lo hi o blk = true → okBlk lo' hi' o blk = true
  | _, [], _ => rfl
  | o, (d, z) :: ds, h => by
    have hoff : ∀ k, offOk lo hi k = true → offOk lo' hi' k = true := fun k hk => by
      simp only [offOk, decide_eq_true_eq] at hk ⊢; omega
    unfold okBlk at h ⊢
    split at h
    · rename_i a ha
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨⟨hok, ht⟩, hr⟩ := h
      refine ⟨⟨?_, ht⟩, okBlk_widen hl hh hr⟩
      cases a <;> simp only [AI.ok, Bool.and_eq_true] at hok ⊢ <;>
        first
        | exact hoff _ hok
        | exact ⟨hoff _ hok.1, hok.2⟩
        | exact hok
        | (split at hok <;> simp_all)
        | (obtain ⟨h1, h2⟩ := hok; split at h1 <;> simp_all)
    · cases h

/-- **`print`'s argument block and call in a frame's code**: the cells
before the multiply at `pc`, the multiply's cell at `pc1` (`zM` bytes), the
cells after it at `pc2`, the `call scc_rt_print` cell at `pc3` (`zc`
bytes). -/
structure PBlk where
  pc : Int64
  pre : List (Directive × Nat)
  pc1 : Int64
  zM : Nat
  pc2 : Int64
  post : List (Directive × Nat)
  pc3 : Int64
  zc : Nat

namespace PBlk

variable (lab : String → Int64) (fr : Scc.Emit.X64.Frame) (b : PBlk) (J : AS → Ctl → Prop)

/-- The state at the multiply from `σ0`. -/
def st1 (σ0 : AS) : AS := (arun lab b.pre ⟨b.pc, oB fr, σ0⟩).σ

/-- The state at the `call` from `σ0`, the multiply's flags `fl`. -/
def st3 (σ0 : AS) (fl : StatusFlags) : AS := (arun lab b.post ⟨b.pc2, oB fr, mulFI.step (b.st1 lab fr σ0) fl⟩).σ

/-- The state at `print`'s entry from `σ0`, the multiply's flags `fl`. -/
def stC (σ0 : AS) (fl : StatusFlags) : AS := (arun lab [(callD, b.zc)] ⟨b.pc3, oB fr, b.st3 lab fr σ0 fl⟩).σ

/-- The block's entry node. -/
def n0 : ND := ⟨b.pc, oB fr, J⟩

/-- The multiply's node. -/
def nM : ND := ⟨b.pc1, oB fr, fun σ c => ∃ σ0, J σ0 c ∧ σ = b.st1 lab fr σ0⟩

/-- The node after the multiply. -/
def n2 : ND := ⟨b.pc2, oB fr, fun σ c => ∃ σ0 fl, J σ0 c ∧ σ = mulFI.step (b.st1 lab fr σ0) fl⟩

/-- The `call`'s node. -/
def n3 : ND := ⟨b.pc3, oB fr, fun σ c => ∃ σ0 fl, J σ0 c ∧ σ = b.st3 lab fr σ0 fl⟩

/-- **The call node**: `print`'s label, `%rsp` past the pushed return
address. -/
def nC : ND := ⟨lab "scc_rt_print", ⟨-(fr.size : Int) - 8, []⟩, fun σ c => ∃ σ0 fl, J σ0 c ∧ σ = b.stC lab fr σ0 fl⟩

end PBlk

/-! ## `callBlock`'s `.print` case -/

/-- `print`'s argument block's directives before the multiply
(`printArgs_runs`). -/
def preD (lO lB lL lM l8 : List Item) (olo os : Int) : List Directive :=
  dirs lO ++ [ext32D, stDir olo] ++ (dirs lB ++ dirs lL ++ [addD, stDir os]) ++ (dirs lM ++ dirs l8)

/-- `print`'s argument block's directives after the multiply
(`printArgs_runs`). -/
def postD (lN lC lN' lC' lS lK : List Item) (ocap okk : Int) : List Directive :=
  [stDir ocap] ++ (dirs lN ++ dirs lC ++ dirs lN' ++ dirs lC' ++ [cmpD, movRsiD, cmovD .c, stDir okk]) ++
    (dirs lS ++ dirs lK)

/-- **The block's cells at `pc`**: the directives `D1` at sizes `zs1`, the
multiply (`zM` bytes), `D2` at sizes `zs2`, the `call` (`zc` bytes), laid
out one after the other. -/
def pblk (pc : Int64) (D1 : List Directive) (zs1 : List Nat) (zM : Nat) (D2 : List Directive) (zs2 : List Nat)
    (zc : Nat) : PBlk :=
  ⟨pc, D1.zip zs1, pc + Int64.ofNat zs1.sum, zM, pc + Int64.ofNat zs1.sum + Int64.ofNat zM, D2.zip zs2,
    pc + Int64.ofNat zs1.sum + Int64.ofNat zM + Int64.ofNat zs2.sum, zc⟩

/-- An operand's value at a state's slots, as a number (`0` when not
placed). -/
def opdNat (fr : Scc.Emit.X64.Frame) (σ : AS) (o : Scc.IR.Operand) : Nat := (opdVal (rsOf fr) σ.slot o).getD 0

/-- An operand off the written registers reads the same at slots kept at
their cells. -/
theorem opdVal_keptX {fr : Scc.Emit.X64.Frame} {lo s cap kk : Scc.IR.Reg} {sl sl' : Int → BitVec 64}
    {a : Scc.IR.Operand} (ha : ∀ r, a = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap ∧ r ≠ kk)
    (hsl : ∀ q j, rsOf fr q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk → sl' j = sl j) :
    opdVal (rsOf fr) sl' a = opdVal (rsOf fr) sl a := by
  cases a with
  | imm => rfl
  | reg r =>
    simp only [opdVal]
    cases hr : rsOf fr r with
    | none => rfl
    | some j => simp only [Option.map_some]; rw [hsl r j hr (ha r rfl)]

/-- **The count passed to `print`** is `printN` of the operands' values,
when `8·m` is below `2^63`. -/
theorem printN_of_rsi {vn vm : BitVec 64} (hm : 8 * vm.toNat < 2 ^ 63) :
    (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64).toNat = printN vn.toNat vm.toNat := by
  have h8 : (vm * 8#64).toNat = vm.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; omega
  unfold printN
  split <;> omega

section Facts

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (lab : String → Int64)

include hf h1 in
/-- **The block with its call runs to `print`'s entry** (`printArgs_runs`
and `call`): before the multiply to `pc1`, after it to `pc3` at any flags;
at `print`'s entry `%rdi` is `b + lo(o)`, `%rsi` is `min(n, 8·m)`
(unsigned, wrapping), the return address `pc3 + zc` below the frame, every
cell but the block's fresh registers' kept. -/
theorem stC_facts {lo s cap kk : Scc.IR.Reg} {olo os ocap okk : Int} (hlo : rsOf fr lo = some olo)
    (hs : rsOf fr s = some os) (hcap : rsOf fr cap = some ocap) (hk : rsOf fr kk = some okk)
    {o b m n : Scc.IR.Operand} {lO lB lL lM l8 lN lC lN' lC' lS lK : List Item}
    (hO : getOp fr .rax o = .ok lO) (hB : getOp fr .rax b = .ok lB) (hL : getOp fr .rcx (.reg lo) = .ok lL)
    (hM : getOp fr .rax m = .ok lM) (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8)
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi (.reg s) = .ok lS)
    (hK : getOp fr .rsi (.reg kk) = .ok lK)
    (hb : ∀ r, b = .reg r → r ≠ lo) (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s)
    (hn : ∀ r, n = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap) (hsc : s ≠ cap) (hsk : s ≠ kk)
    {pc : Int64} {zs1 zs2 : List Nat} {zM zc : Nat}
    (hz1 : zs1.length = (preD lO lB lL lM l8 olo os).length)
    (hz2 : zs2.length = (postD lN lC lN' lC' lS lK ocap okk).length) (σ0 : AS) :
    ∃ vb vo vm vn : BitVec 64, opdVal (rsOf fr) σ0.slot b = some vb.toNat ∧
      opdVal (rsOf fr) σ0.slot o = some vo.toNat ∧ opdVal (rsOf fr) σ0.slot m = some vm.toNat ∧
      opdVal (rsOf fr) σ0.slot n = some vn.toNat ∧
      (∃ σ1, arun lab ((preD lO lB lL lM l8 olo os).zip zs1) ⟨pc, oB fr, σ0⟩ =
        ⟨pc + Int64.ofNat zs1.sum, oB fr, σ1⟩) ∧
      ∀ fl,
      let b' := pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc
      (∃ σ3, arun lab b'.post ⟨b'.pc2, oB fr, mulFI.step (b'.st1 lab fr σ0) fl⟩ = ⟨b'.pc3, oB fr, σ3⟩) ∧
      (b'.stC lab fr σ0 fl).regs.get64 .rdi = vb + (vo.take 32).setWidth 64 ∧
      (b'.stC lab fr σ0 fl).regs.get64 .rsi = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
      (b'.stC lab fr σ0 fl).slot (-(fr.size : Int) - 8) = (b'.pc3 + Int64.ofNat zc).toBitVec ∧
      ∀ q j, rsOf fr q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk → (b'.stC lab fr σ0 fl).slot j = σ0.slot j := by
  obtain ⟨vb, vo, vm, vn, hvb, hvo, hvm, hvn, r⟩ :=
    printArgs_runs hf h1 lab hlo hs hcap hk hO hB hL hM h8 hN hC hN' hC' hS hK hb hm hn hsc hsk σ0
  obtain ⟨σ1, e1, hP⟩ := r zs1 pc hz1
  replace e1 : arun lab ((preD lO lB lL lM l8 olo os).zip zs1) ⟨pc, oB fr, σ0⟩ =
    ⟨pc + Int64.ofNat zs1.sum, oB fr, σ1⟩ := e1
  refine ⟨vb, vo, vm, vn, hvb, hvo, hvm, hvn, ⟨σ1, e1⟩, fun fl => ?_⟩
  have hst1 : (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc).st1
      lab fr σ0 = σ1 := by
    simp only [PBlk.st1, pblk]; rw [e1]
  obtain ⟨σ3, e3, hd, hsi, hsl⟩ := hP fl zs2 (pc + Int64.ofNat zs1.sum + Int64.ofNat zM) hz2
  replace e3 : arun lab ((postD lN lC lN' lC' lS lK ocap okk).zip zs2)
      ⟨pc + Int64.ofNat zs1.sum + Int64.ofNat zM, oB fr, mulFI.step σ1 fl⟩ =
    ⟨pc + Int64.ofNat zs1.sum + Int64.ofNat zM + Int64.ofNat zs2.sum, oB fr, σ3⟩ := e3
  have hst3 : (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc).st3
      lab fr σ0 fl = σ3 := by
    simp only [PBlk.st3, hst1]; simp only [pblk]; rw [e3]
  have hC : (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc).stC
      lab fr σ0 fl = ⟨σ3.regs.set64 .rsp (σ3.regs.get64 .rsp - 8#64), σ3.zmms, σ3.status, upd σ3.slot
        (-(fr.size : Int) - 8)
        (pc + Int64.ofNat zs1.sum + Int64.ofNat zM + Int64.ofNat zs2.sum + Int64.ofNat zc).toBitVec⟩ := by
    simp only [PBlk.stC, hst3, arun_callD]; rfl
  refine ⟨⟨σ3, by simp only [hst1]; simp only [pblk]; rw [e3]⟩, ?_, ?_, ?_, ?_⟩
  · rw [hC]; show (σ3.regs.set64 .rsp _).get64 .rdi = _; rw [Reg64s.get64_set64_ne _ (by decide), hd]
  · rw [hC]; show (σ3.regs.set64 .rsp _).get64 .rsi = _; rw [Reg64s.get64_set64_ne _ (by decide), hsi]
  · rw [hC]; simp [Spike.Lib.upd_apply, pblk]
  · intro q j hq hfr
    have hb := rsOf_bounds hf hq
    rw [hC]
    simp only [Spike.Lib.upd_apply]
    split
    · omega
    · exact hsl j fun q' hq' => (rsOf_inj hf hq hq') ▸ hfr

end Facts

section Seg

variable {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`print`'s argument block, its call and `print`'s run are one segment
inside `W`** (any blocks): from the block's entry node (`PBlk.n0`, the
body's offsets `oB fr`) the cells before the multiply (`hr1`), the multiply
(`mulFI`, a flag node), the cells after it ending in the `call` (`hr2`) to
the call node `PBlk.nC`, then `print_call_segW` with its premises at
`PBlk.nC`. -/
theorem print_blocks_segW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {fr : Scc.Emit.X64.Frame} (h8 : (fr.size : Int) % 8 = 0) {b : PBlk} {J : AS → Ctl → Prop} {lo hi : Int}
    (hne1 : b.pre ≠ []) (hne2 : b.post ≠ [])
    (hok1 : okBlk lo hi (oB fr) b.pre = true) (hok2 : okBlk lo hi (oB fr) b.post = true)
    (hcode1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s b.pc b.pre)
    (hcodeM : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s b.pc1 [(mulFI.toDir, b.zM)])
    (hcode2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s b.pc2 b.post)
    (hcode3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s b.pc3 [(callD, b.zc)])
    (hW1 : BlkW W K exe endPc R F (b.n0 fr J) b.pre)
    (hWM : NodeW W K exe endPc R F (b.nM (_root_.Executable.labels exe).label fr J))
    (hW2 : BlkW W K exe endPc R F (b.n2 (_root_.Executable.labels exe).label fr J) b.post)
    (hW3 : BlkW W K exe endPc R F (b.n3 (_root_.Executable.labels exe).label fr J) [(callD, b.zc)])
    (hr1 : ∀ σ0 c, J σ0 c → ∃ σ1,
      arun (_root_.Executable.labels exe).label b.pre ⟨b.pc, oB fr, σ0⟩ = ⟨b.pc1, oB fr, σ1⟩)
    (hpc2 : b.pc2 = b.pc1 + Int64.ofNat b.zM)
    (hr2 : ∀ σ0 c fl, J σ0 c → ∃ σ', arun (_root_.Executable.labels exe).label b.post
      ⟨b.pc2, oB fr, mulFI.step (b.st1 (_root_.Executable.labels exe).label fr σ0) fl⟩ = ⟨b.pc3, oB fr, σ'⟩)
    {nC : ND} (hnC : nC = b.nC (_root_.Executable.labels exe).label fr J)
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hlo' : R.lo ≤ -(fr.size : Int) - 56) (hhi' : -(fr.size : Int) ≤ R.hi)
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.X64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c0 => ∃ mw b, c0 = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F (b.n0 fr J)) (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  have hosp : nC.o.sp = -(fr.size : Int) - 8 := by rw [hnC]; rfl
  refine SegW.seq (Q := At exe endPc R F (b.nM lab fr J)) ?_ (SegW.seq (Q := At exe endPc R F (b.n2 lab fr J)) ?_
    (SegW.seq (Q := At exe endPc R F nC) ?_
      (print_call_segW hp hend hprog hF hR (by rw [hosp]; omega) (by rw [hosp]; omega)
        (by rw [hosp]; omega) (by rw [hnC]; rfl) hP0 hN hm hW hd hE hK hcl
        (fun σC c hJ F' _ => hWs σC c hJ F') (fun σC c hJ F' _ => hlb σC c hJ F')
        (fun σC c hJ F' _ => hwe σC c hJ F') hret habort)))
  · refine (seg_ndW (N := fun _ : Unit => b.nM lab fr J) (E := fun e : Empty => e.elim) hne1 hok1 hF hR hlo hhi
      hcode1 hW1 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
        fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    obtain ⟨σ1, e⟩ := hr1 σ c hJ
    refine ⟨?_, ?_, σ, hJ, ?_⟩
    · show b.pc1 = (arun lab b.pre ⟨b.pc, oB fr, σ⟩).pc
      rw [e]
    · show SO.le (oB fr) (arun lab b.pre ⟨b.pc, oB fr, σ⟩).so = true
      rw [e]; simp [SO.le, oB, lk]
    · rfl
  · refine (flag_ndW (N := fun _ : Unit => b.n2 lab fr J) (E := fun e : Empty => e.elim) (fi := mulFI) (z := b.zM)
      rfl hF hcodeM hWM fun σ c ⟨σ0, hJ0, hσ⟩ fl => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ0, fl, hJ0, by rw [hσ]⟩⟩).mono_post
        fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · exact hpc2
    · simp [PBlk.n2, PBlk.nM, SO.le, oB, lk, FI.so, FI.dst, SO.kill, rm]
  · refine SegW.seq (Q := At exe endPc R F (b.n3 lab fr J)) ?_ ?_
    · refine (seg_ndW (N := fun _ : Unit => b.n3 lab fr J) (E := fun e : Empty => e.elim) hne2 hok2 hF hR hlo hhi
        hcode2 hW2 fun σ c ⟨σ0, fl, hJ0, hσ⟩ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
          fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
      obtain ⟨σ', e⟩ := hr2 σ0 c fl hJ0
      subst hσ
      refine ⟨?_, ?_, σ0, fl, hJ0, rfl⟩
      · show b.pc3 = (arun lab b.post ⟨b.pc2, oB fr, mulFI.step (b.st1 lab fr σ0) fl⟩).pc
        rw [e]
      · show SO.le (oB fr) (arun lab b.post ⟨b.pc2, oB fr, mulFI.step (b.st1 lab fr σ0) fl⟩).so = true
        rw [e]; simp [SO.le, oB, lk]
    · refine (seg_ndW (N := fun _ : Unit => nC) (E := fun e : Empty => e.elim) (lo := -(fr.size : Int) - 8)
        (hi := -(fr.size : Int)) (by simp) (okBlk_callD (decide_eq_true (by simp only [PBlk.n3, oB]; omega))) hF hR
        (by omega) hhi'
        hcode3 hW3 fun σ c ⟨σ0, fl, hJ0, hσ⟩ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
          fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
      subst hnC hσ
      refine ⟨?_, ?_, σ0, fl, hJ0, rfl⟩
      · show lab "scc_rt_print" = (arun lab [(callD, b.zc)] ⟨b.pc3, oB fr, b.st3 lab fr σ0 fl⟩).pc
        rw [arun_callD]
      · show SO.le ⟨-(fr.size : Int) - 8, []⟩ (arun lab [(callD, b.zc)] ⟨b.pc3, oB fr, b.st3 lab fr σ0 fl⟩).so = true
        rw [arun_callD]; simp [SO.le, oB]

/-- **`print`'s argument block (`callBlock`'s `.print` case), its call and
`print`'s run are one segment inside `W`**, from the block's entry node at
`pc` (the body's offsets `oB fr`, invariant `J`) in any caller's frame:
`print_blocks_segW` at the block's cells `B` (`pblk`: `preD` at sizes
`zs1`, the multiply, `postD` at sizes `zs2`, the `call`), its runs and
coverage from `stC_facts` and `covP_printPre`/`covP_printPost`, with
`print`'s count and slice length the operands `n`, `m`'s values at the call
state (`opdNat`; the count's `printN` is discharged from the block's
`min(n, 8·m)`). The caller gives the block's code and states inside `W`,
and `print_call_segW`'s remaining premises at the call node `B.nC`. -/
theorem print_block_segW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h8s : (fr.size : Int) % 8 = 0)
    {lo s cap kk : Scc.IR.Reg} {olo os ocap okk : Int} (hlo : rsOf fr lo = some olo)
    (hs : rsOf fr s = some os) (hcap : rsOf fr cap = some ocap) (hk : rsOf fr kk = some okk)
    {o b m n : Scc.IR.Operand} {lO lB lL lM l8 lN lC lN' lC' lS lK : List Item}
    (hO : getOp fr .rax o = .ok lO) (hB : getOp fr .rax b = .ok lB) (hL : getOp fr .rcx (.reg lo) = .ok lL)
    (hM : getOp fr .rax m = .ok lM) (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8)
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi (.reg s) = .ok lS)
    (hKk : getOp fr .rsi (.reg kk) = .ok lK)
    (hb : ∀ r, b = .reg r → r ≠ lo) (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap ∧ r ≠ kk)
    (hn : ∀ r, n = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap ∧ r ≠ kk) (hsc : s ≠ cap) (hsk : s ≠ kk)
    {pc : Int64} {zs1 zs2 : List Nat} {zM zc : Nat}
    (hz1 : zs1.length = (preD lO lB lL lM l8 olo os).length)
    (hz2 : zs2.length = (postD lN lC lN' lC' lS lK ocap okk).length)
    {B : PBlk} (hBk : B = pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc)
    {J : AS → Ctl → Prop}
    (hcode1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s B.pc B.pre)
    (hcodeM : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s B.pc1 [(mulFI.toDir, B.zM)])
    (hcode2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s B.pc2 B.post)
    (hcode3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s B.pc3 [(callD, B.zc)])
    (hW1 : BlkW W K exe endPc R F (B.n0 fr J) B.pre)
    (hWM : NodeW W K exe endPc R F (B.nM (_root_.Executable.labels exe).label fr J))
    (hW2 : BlkW W K exe endPc R F (B.n2 (_root_.Executable.labels exe).label fr J) B.post)
    (hW3 : BlkW W K exe endPc R F (B.n3 (_root_.Executable.labels exe).label fr J) [(callD, B.zc)])
    {nC : ND} (hnC : nC = B.nC (_root_.Executable.labels exe).label fr J)
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop} {pw wn : AS → TermRun.Word}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo' : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (opdNat fr σ n) (opdNat fr σ m) 0 c)
    (hm8 : ∀ σ c, nC.J σ c → 8 * opdNat fr σ m < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn (opdNat fr · n) (opdNat fr · m) σC)
      (pcS pw wn (opdNat fr · n) (opdNat fr · m) σC) W K exe endPc (pR (nC.o.sp - 8) R) (pF (nC.o.sp - 8) R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.X64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn (opdNat fr · n) (opdNat fr · m))
        (pcS pw wn (opdNat fr · n) (opdNat fr · m)) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn (opdNat fr · n) (opdNat fr · m))
        (pcS pw wn (opdNat fr · n) (opdNat fr · m)) nC.o.sp σC .sys) s c' →
      ∀ k j, k + j < printN (opdNat fr σC n) (opdNat fr σC m) →
      BO s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (opdNat fr σC m) (k + j))
        (fun c0 => ∃ mw b, c0 = nextC (pw σC) (wn σC) (opdNat fr σC m) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn (opdNat fr · n) (opdNat fr · m))
        (pcS pw wn (opdNat fr · n) (opdNat fr · m)) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (opdNat fr σC n) (opdNat fr σC m) k c1 → WE s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (opdNat fr σC n) (opdNat fr σC m) (printN (opdNat fr σC n) (opdNat fr σC m)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 →
      PrintC (pw σC) (wn σC) (opdNat fr σC n) (opdNat fr σC m) k c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F (B.n0 fr J)) (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  have fx := fun σ0 => stC_facts hf h1 lab hlo hs hcap hk hO hB hL hM h8 hN hC hN' hC' hS hKk hb
    (fun r h => ⟨(hm r h).1, (hm r h).2.1⟩) (fun r h => ⟨(hn r h).1, (hn r h).2.1, (hn r h).2.2.1⟩) hsc hsk
    (pc := pc) (zM := zM) (zc := zc) hz1 hz2 σ0
  have hcnt : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (opdNat fr σ n) (opdNat fr σ m) := by
    intro σ c hJ
    have hJ' := hJ
    rw [hnC, hBk] at hJ'
    obtain ⟨σ0, fl, -, rfl⟩ := hJ'
    obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, hrest⟩ := fx σ0
    obtain ⟨-, -, hsi, -, hsl⟩ := hrest fl
    have en : opdNat fr (PBlk.stC lab fr (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM
        (postD lN lC lN' lC' lS lK ocap okk) zs2 zc) σ0 fl) n = vn.toNat := by
      simp only [opdNat]; rw [opdVal_keptX hn hsl, hvn]; rfl
    have em : opdNat fr (PBlk.stC lab fr (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM
        (postD lN lC lN' lC' lS lK ocap okk) zs2 zc) σ0 fl) m = vm.toNat := by
      simp only [opdNat]; rw [opdVal_keptX hm hsl, hvm]; rfl
    have h8' := hm8 _ c hJ
    rw [em] at h8'
    rw [en, em, hsi, printN_of_rsi h8']
  subst hBk
  refine print_blocks_segW h8s (lo := -(fr.size : Int)) (hi := 16) ?_ ?_
    ((covP_printPre hf h1 hlo hs hO hB hL hM h8).ok hz1) ((covP_printPost hf h1 hcap hk hN hC hN' hC' hS hKk).ok hz2)
    hcode1 hcodeM hcode2 hcode3 hW1 hWM hW2 hW3
    (fun σ0 _ _ => by obtain ⟨_, _, _, _, _, _, _, _, hr, _⟩ := fx σ0; exact hr) rfl
    (fun σ0 _ fl _ => by obtain ⟨_, _, _, _, _, _, _, _, _, hr⟩ := fx σ0; exact (hr fl).1) hnC hp hend hprog hF hR
    (by omega) hhi hlo' (by omega)
    hP0 hcnt hm8 hW hd hE hK hcl hWs hlb hwe hret habort
  · intro h
    have := congrArg List.length h
    simp [pblk, List.length_zip, hz1, preD] at this
  · intro h
    have := congrArg List.length h
    simp [pblk, List.length_zip, hz2, postD] at this

end Seg

end Spike.Lib.LowerX64
