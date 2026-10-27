/-
**An output call of an `Accepted2` body** (x86-64): `printCallC_of`, the
obligation `PrintCallC` (`Body2.lean`) at the node with buffers and slices
(`bodyN2`), from `printInsts`' code (`print_codeC`), the states of its
blocks and of `scc_rt_print` inside the frame's fragment (`PrintW`,
`PrintWE`), and where an abort of `print` lands (`hAb`).

The source's call is taken first (`SegWS.pre_run`): at the `let` the
source runs locally to the call site `c1`, calls `print` (the frame
`printFrame x e c1` pushed) and runs to the top of `printL`
(`printCall_enter`), or, for an empty slice, to `print`'s `ret ()`. The
argument block, the `call` and `print`'s run are then one segment at the
frames with `print`'s, the thread pointer kept (`print_call_segW_tp`,
`print_call_emptyW_tp`); after the return the source binds `x` to `()` and
pops the frame (`printCall_exit`, `printCall_ret`; `SegWS.post_run`). The
ghost run passes the call as a memory let (`FrameRunM.mem1`).

- `PBlk.nCR`, `print_blocks_toC`: the argument block and the `call` to
  `print`'s entry (the first three segments of `print_blocks_segW`), the
  caller's `%rbp` at the frame's record;
- `stC_slots`: at `print`'s entry every cell but the block's fresh
  registers' and the return address's is kept (`printArgs_runs`);
- `NodeJE.unitBind`, `NJB.printUnit`: the node invariant after the call,
  `x` bound to `()` with no words;
- `printJL`, `printJ`, `PrintW`, `PrintWE`: the caller's facts at the call
  site, the block's invariant, and the states inside the frame's fragment;
- `PrintCodeC.toPrintCode`: the block's cells from its chunks (`PrintW`,
  `PrintWE` quantify over blocks laid out from the chunks' sizes);
- `printCallC_of`;
- `PrintSlotsA`, `PrintLen`, `printCallC_ofA`: the caller's slots at every
  state of the argument block and the count's bound, given to `PrintW'`,
  `PrintWE'` (`printCallC_of'` its wrapper).
-/
import Spike.Lib.LowerX64.PrintCallC2Code
import Spike.Lib.LowerX64.CallC2
import Spike.Lib.X64PrintTP
import Spike.Lib.Src.PrintCallSrc
import Spike.Lib.Src.PrintSite
import Spike.Lib.LowerX64.CtxC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (S E Item i64 i32 xr or_)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv opdVal_upd WordsRep SRep lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName atomV)
open Scc.Sem (ValRep)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.X64.PrintA (PrintAW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.LowerShape (printInsts)

set_option linter.unusedSimpArgs false

/-! ## The argument block to `print`'s entry -/

/-- **The call node with the caller's `%rbp`**: `PBlk.nC`, `%rbp` at the
caller's frame record. -/
def PBlk.nCR (lab : String → Int64) (fr : Scc.Emit.X64.Frame) (b : PBlk) (J : AS → Ctl → Prop) (R : Region) : ND :=
  ⟨lab "scc_rt_print", ⟨-(fr.size : Int) - 8, []⟩, fun σ c => (b.nC lab fr J).J σ c ∧ σ.regs.get64 .rbp = R.addr 0⟩

section Seg

variable {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The argument block and its `call` are one segment inside `W`**, to
`print`'s entry (`print_blocks_segW` without `print`'s run): the cells
before the multiply, the multiply, the cells after it and the `call`, to
`PBlk.nCR` (the caller's `%rbp` read off the frame's offsets before the
`call`, which keeps it). -/
theorem print_blocks_toC {W : Frag isa} {K : State → State → Prop}
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
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hlo' : R.lo ≤ -(fr.size : Int) - 8) (hhi' : -(fr.size : Int) ≤ R.hi) :
    SegW W K p lbl ms (At exe endPc R F (b.n0 fr J))
      (At exe endPc R F (b.nCR (_root_.Executable.labels exe).label fr J R)) := by
  let lab := (_root_.Executable.labels exe).label
  let n3R : ND := ⟨b.pc3, oB fr, fun σ c => (b.n3 lab fr J).J σ c ∧ σ.regs.get64 .rbp = R.addr 0⟩
  refine SegW.seq (Q := At exe endPc R F (b.nM lab fr J)) ?_ (SegW.seq (Q := At exe endPc R F (b.n2 lab fr J)) ?_
    (SegW.seq (Q := At exe endPc R F (b.n3 lab fr J)) ?_ ?_))
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
  · have hok3 : okBlk (-(fr.size : Int) - 8) (-(fr.size : Int)) (oB fr) [(callD, b.zc)] = true :=
      okBlk_callD (decide_eq_true (by simp only [oB]; omega))
    refine SegW.mono_pre ((seg_ndW (n := n3R) (N := fun _ : Unit => b.nCR lab fr J R)
      (E := fun e : Empty => e.elim) (lo := -(fr.size : Int) - 8) (hi := -(fr.size : Int)) (by simp) hok3 hF hR hlo'
      hhi' hcode3 (BlkW.mono hW3 rfl rfl fun _ _ h => h.1) fun σ c ⟨⟨σ0, fl, hJ0, hσ⟩, hbp⟩ =>
        ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
          fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) fun s c h => ?_
    · subst hσ
      refine ⟨?_, ?_, ⟨σ0, fl, hJ0, rfl⟩, ?_⟩
      · show lab "scc_rt_print" = (arun lab [(callD, b.zc)] ⟨b.pc3, oB fr, b.st3 lab fr σ0 fl⟩).pc
        rw [arun_callD]
      · show SO.le ⟨-(fr.size : Int) - 8, []⟩ (arun lab [(callD, b.zc)] ⟨b.pc3, oB fr, b.st3 lab fr σ0 fl⟩).so = true
        rw [arun_callD]; simp [SO.le, oB]
      · show (arun lab [(callD, b.zc)] ⟨b.pc3, oB fr, b.st3 lab fr σ0 fl⟩).σ.regs.get64 .rbp = R.addr 0
        rw [arun_callD]
        show (Reg64s.set64 _ .rsp _).get64 .rbp = _
        rw [Reg64s.get64_set64_ne _ (by decide)]; exact hbp
    · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
      exact ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hA.so .rbp 0 (by simp [PBlk.n3, oB, SO.get, lk])⟩

end Seg

/-! ## The cells at `print`'s entry -/

section Facts

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (lab : String → Int64)

include hf h1 in
/-- **At `print`'s entry every cell but the block's fresh registers' and
the return address's is kept** (`printArgs_runs`' cells, the `call`'s
push at `-size - 8`). -/
theorem stC_slots {lo s cap kk : Scc.IR.Reg} {olo os ocap okk : Int} (hlo : rsOf fr lo = some olo)
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
    (hz2 : zs2.length = (postD lN lC lN' lC' lS lK ocap okk).length) (σ0 : AS) (fl : StatusFlags)
    (j : Int) (hj8 : j ≠ -(fr.size : Int) - 8) (hj : ∀ q, rsOf fr q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk) :
    ((pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc).stC
      lab fr σ0 fl).slot j = σ0.slot j := by
  obtain ⟨vb, vo, vm, vn, -, -, -, -, r⟩ :=
    printArgs_runs hf h1 lab hlo hs hcap hk hO hB hL hM h8 hN hC hN' hC' hS hK hb hm hn hsc hsk σ0
  obtain ⟨σ1, e1, hP⟩ := r zs1 pc hz1
  replace e1 : arun lab ((preD lO lB lL lM l8 olo os).zip zs1) ⟨pc, oB fr, σ0⟩ =
    ⟨pc + Int64.ofNat zs1.sum, oB fr, σ1⟩ := e1
  have hst1 : (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc).st1
      lab fr σ0 = σ1 := by
    simp only [PBlk.st1, pblk]; rw [e1]
  obtain ⟨σ3, e3, -, -, hsl⟩ := hP fl zs2 (pc + Int64.ofNat zs1.sum + Int64.ofNat zM) hz2
  replace e3 : arun lab ((postD lN lC lN' lC' lS lK ocap okk).zip zs2)
      ⟨pc + Int64.ofNat zs1.sum + Int64.ofNat zM, oB fr, mulFI.step σ1 fl⟩ =
    ⟨pc + Int64.ofNat zs1.sum + Int64.ofNat zM + Int64.ofNat zs2.sum, oB fr, σ3⟩ := e3
  have hst3 : (pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc).st3
      lab fr σ0 fl = σ3 := by
    simp only [PBlk.st3, hst1]; simp only [pblk]; rw [e3]
  simp only [PBlk.stC, hst3, arun_callD, Spike.Lib.upd_apply, oB]
  split
  · omega
  · exact hsl j hj

/-- **At `print`'s entry the `%fs` base is the block's entry's** (no covered
instruction writes it, `arun_fsBase`). -/
theorem stC_fsBase (b : PBlk) (σ0 : AS) (fl : StatusFlags) :
    (b.stC lab fr σ0 fl).regs.fsBase = σ0.regs.fsBase := by
  simp only [PBlk.stC, PBlk.st3, PBlk.st1, arun_fsBase, FI.step, FI.regs, mulFI, Reg64s.set64_fsBase]

end Facts

/-! ## The source after the call -/

section Src

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {rs : Scc.IR.Reg → Option Int}

/-- **`x` bound to `()` after a call** (the node part): `NodeJE` at the
call site `c1`, the cells of the bindings' operands kept (`hsl`). Then
`NodeJE` at `e` with `x` bound to no words. -/
theorem NodeJE.unitBind {x : String} {op : Op} {e : Expr} {s : SEnv} {sl sl' : Int → BitVec 64} {c1 : Ctl}
    (hj : NodeJE lbl rs (.let_ x op e) s sl c1)
    (hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    NodeJE lbl rs e ((x, .unit, []) :: s) sl' ⟨e, (x, .unit, []) :: c1.env, none⟩ :=
  ⟨rfl, rfl, (hj.2.2.congr hsl).bind x rfl trivial⟩

/-- **`let x = g(a)` of a call of `print`**: the node's parts at the call
site `c1` (`NodeJE`, `EnvLit`, `EnvB`, `MemB`, `EnvSmall`), the cells of the
bindings' operands kept (`hsl`). Then `NJB` at `e` with `x` bound to `()`,
the walk's next state at `()`'s layout `.nil`. -/
theorem NJB.printUnit {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {B : Nat}
    {x g : String} {is : List String} {a : At} {ts : List Ty} {e : Expr} {s : SEnv} {sl sl' : Int → BitVec 64}
    {c1 : Ctl} (hj : NodeJE lbl rs (.let_ x (.call g is a ts) e) s sl c1) (hn : EnvLit lits c1.env)
    (hb : EnvB lits cs bufs L sm lsize c1.env) (hm : MemB L sm B) (hS : EnvSmall c1.env)
    (hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    NJB p lbl rs ((x, .nil) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
      (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)) L sm lsize B e ((x, .unit, []) :: s) sl'
      ⟨e, (x, .unit, []) :: c1.env, none⟩ :=
  ⟨_, .refl _, NodeJE.unitBind hj hsl, hn.cons rfl (fun _ _ h _ => by simp at h),
    hb.cons (SliceL.nil _) (fun _ h => by rcases h with h | h <;> cases h) (fun _ _ h => by cases h), hm,
    EnvSmall.cons hS (fun _ h => by simp at h)⟩

/-- **An empty slice, the call**: the call and `print`'s body to its
`ret ()` (`printCall_empty` before the return). -/
theorem printCall_emptyR {c : Ctl} {fs : List TermRun.Frame} {x : String} {is : List String} {a : At} {e : Expr}
    {t : Ty} {pw wm wn : TermRun.Word}
    (hp : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (ht : c.term = .let_ x (.call "print" is a []) e) (ha : TermRun.evalAt c.env a = some (t, [pw, wm, wn]))
    (hwm : wm.val = .num 0) :
    ∃ env, FrameRun p (c, fs) (⟨.ret .unit, env, none⟩, printFrame x e c :: fs) := by
  have hr : ∃ env, LocalRunS p ⟨Spike.Lib.PrintSrc.printBody, [("a", Spike.Lib.Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨.ret .unit, env, none⟩ :=
    ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
      .single (localStepS_ifeq_eq rfl rfl rfl hwm rfl)⟩
  obtain ⟨env, hr⟩ := hr
  exact ⟨env, .step (printCall_step hp ht ha) (FrameRun.ofLocalS hr _)⟩

end Src

/-! ## The nodes and the states inside the frame's fragment -/

/-- **The caller's facts at a call of `print`**, at the call site `c1`:
the node invariant at the `let` (`t`, `env`) with the walk's literal, buffer
and size facts, the frame's record, the ghost `c0`'s local run to `c1`, the
thread pointer `tp`. -/
def printJL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64)
    (tp : UInt64) (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) (c1 : Ctl) (σ : AS) : Prop :=
  (∃ L sm B, NodeJE lbl (rsOf fr) t (ofEnv2 env) σ.slot c1 ∧ EnvLit lits c1.env ∧ EnvB lits cs bufs L sm lsize c1.env ∧
    MemB L sm B ∧ EnvSmall c1.env) ∧ FrJ fp ra σ.slot ∧ LocalRun p c0 c1 ∧ σ.regs.fsBase = tp

/-- **The argument block's invariant**: the source at `print`'s control
`cE` (the call taken), the caller's facts at `c1` (`printJL`). -/
def printJ (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64)
    (tp : UInt64) (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) (c1 cE : Ctl) : AS → Ctl → Prop :=
  fun σ c => c = cE ∧ printJL p lbl lsize fr fp ra tp c0 t env lits cs bufs c1 σ

/-- **`printInsts`' code at `pc`** as `pblk`'s cells (`print_code`'s data):
the fresh registers' slots, the operands' loads, the blocks' sizes. -/
def PrintCode (fr : Scc.Emit.X64.Frame) (pc : Int64) (n : Nat) (b : Scc.IR.Operand) (o : Scc.IR.Reg)
    (m cw : Scc.IR.Operand) (B : PBlk) : Prop :=
  ∃ (olo os ocap okk : Int) (lO lB lL lM l8 lN lC lN' lC' lS lK : List Item) (zs1 zs2 : List Nat) (zM zc : Nat),
    rsOf fr (regName "lo" n) = some olo ∧ rsOf fr (regName "s" (n + 1)) = some os ∧
    rsOf fr (regName "cap" (n + 2)) = some ocap ∧ rsOf fr (regName "k" (n + 3)) = some okk ∧
    getOp fr .rax (.reg o) = .ok lO ∧ getOp fr .rax b = .ok lB ∧
    getOp fr .rcx (.reg (regName "lo" n)) = .ok lL ∧ getOp fr .rax m = .ok lM ∧
    getOp fr .rcx (Scc.Lower.imm 8) = .ok l8 ∧ getOp fr .rdx cw = .ok lN ∧
    getOp fr .rsi (.reg (regName "cap" (n + 2))) = .ok lC ∧ getOp fr .rax cw = .ok lN' ∧
    getOp fr .rcx (.reg (regName "cap" (n + 2))) = .ok lC' ∧ getOp fr .rdi (.reg (regName "s" (n + 1))) = .ok lS ∧
    getOp fr .rsi (.reg (regName "k" (n + 3))) = .ok lK ∧
    zs1.length = (preD lO lB lL lM l8 olo os).length ∧ zs2.length = (postD lN lC lN' lC' lS lK ocap okk).length ∧
    B = pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc

/-- **The block's cells from its chunks** (`PrintCodeC` gives `PrintCode`). -/
theorem PrintCodeC.toPrintCode {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk : Nat} {pc : Int64} {n : Nat} {b : Scc.IR.Operand}
    {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk} (h : PrintCodeC fr Cd Bl kk pc n b o m cw B) :
    PrintCode fr pc n b o m cw B := by
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, _, _, _, _, _, _, _, _, _, _, _,
    a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2, zc,
    hlo, hs, hcap, hk, hO, hB, hL, hM, h8, hN, hC, hN', hC', hS, hK, eO, eB, eL, eM, eI, eN, eC, eN', eC', eS, eK,
    -, -, -, -, -, -, rfl⟩ := h
  exact ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, _, _, _, _, hlo, hs, hcap, hk, hO, hB,
    hL, hM, h8, hN, hC, hN', hC', hS, hK,
    by simp only [preD, dirs_append, eO, eB, eL, eM, eI, List.length_append, List.length_cons, List.length_nil],
    by simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.length_append, List.length_cons,
      List.length_nil], rfl⟩

/-- **The argument block's and `print`'s states in `W₀`**, not moved by
`K`, at the block's cells `B` from the invariant `J`: along the cells
before the multiply, at the multiply, along the cells after it, at the
`call`, and `print`'s blocks (`PrintAW` at `print`'s source predicates
`P`, `Q`) for every call state. -/
def PrintBlkW (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame) (B : PBlk) (J : AS → Ctl → Prop)
    (P Q : Nat → Ctl → Prop) : Prop :=
  BlkW W₀ K exe endPc R F (B.n0 fr J) B.pre ∧
    NodeW W₀ K exe endPc R F (B.nM (_root_.Executable.labels exe).label fr J) ∧
    BlkW W₀ K exe endPc R F (B.n2 (_root_.Executable.labels exe).label fr J) B.post ∧
    BlkW W₀ K exe endPc R F (B.n3 (_root_.Executable.labels exe).label fr J) [(callD, B.zc)] ∧
    ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr J).J σC c →
      PrintAW σC.regs.rbp.toBitVec (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rdi) (σC.regs.get64 .rsi).toNat
        P Q W₀ K exe endPc (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)

/-- **A call of `print` of a nonempty slice inside `W₀`** (`print_call_segW`'s
premises at the call): for `printInsts`' code at `pc` as its chunks at the
code predicates `Cd`, `Bl` (`PrintCodeC`, the block's cells' sizes the
chunks'), the block's and `print`'s states (`PrintBlkW` at
`PrintC pw wn nv mv`), and at `print`'s system call (for every call state,
under any frame condition `F'` inside `print`'s, `pF`) the states in `W₀`
not moved by `K`, the memory side's byte steps (`hlb`) and output words
(`hwe`). -/
def PrintW (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop) (kk : Nat)
    (pc : Int64) (n : Nat)
    (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (pw wn : TermRun.Word)
    (nv mv : Nat) : Prop :=
  ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
    PrintBlkW W₀ K exe endPc R F fr B J (PrintC pw wn nv mv) (PrintC pw wn nv mv) ∧
    ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr J).J σC c → (σC.regs.get64 .rsi).toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(fr.size : Int) - 8 - 8) R F md) → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      (W₀ s c' ∧ ∀ s', ¬ K s s') ∧
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1

/-- **The source at `print`'s system call** (`PrintW`'s `.sys` states): the
loop at some byte `k` below the count, `PrintC pw wn nv mv k`, when the call
state's `%rsi` is the count `printN nv mv`. -/
theorem printSys_src {exe : _root_.Executable} {endPc : Int64} {R' : Region} {F' : MachineData → Prop}
    {lab : String → Int64} {ko : Int} {σC : AS} {pw wn : TermRun.Word} {nv mv : Nat} {s : State} {c' : Ctl}
    (hAt : At exe endPc R' F' (pN lab (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) ko σC .sys) s c')
    (hN : (σC.regs.get64 .rsi).toNat = printN nv mv) :
    ∃ k, PrintC pw wn nv mv k c' ∧ k < printN nv mv := by
  obtain ⟨-, -, -, -, σ, -, -, ⟨k, -, hlt, hP⟩, -⟩ := hAt
  exact ⟨k, hP, hN ▸ hlt⟩

/-- **A call of `print` of an empty slice inside `W₀`**: for `printInsts`'
code at `pc` as its chunks (`PrintCodeC`), the block's and `print`'s states
(`PrintBlkW`, `print`'s source at `cE`, its `ret ()`). -/
def PrintWE (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (kk : Nat) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (cE : Ctl) : Prop :=
  ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
    PrintBlkW W₀ K exe endPc R F fr B J (fun _ c => c = cE) (fun _ _ => False)

/-- **The caller's slots at a call of `print`**: at every call state the
caller's control `c1` with `x` bound to `()` before its continuation `e`
placed in the state's slots, at `e`'s immediates `i e`
(`printCallC_of'` gives it to `PrintW'`, `PrintWE'`; with the cells kept by
`print`, the caller's frame placed under `pFJ`). -/
def PrintSlots (lbl : WeakMem.AllocLabel → Option Nat) (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (kk : Nat) (lab : String → Int64) (pc : Int64) (n : Nat) (b : Scc.IR.Operand) (o : Scc.IR.Reg)
    (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (x : String) (e : Expr) (c1 : Ctl) : Prop :=
  ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC lab fr J).J σC c →
    SlotRepAt (fun _ => i e) lbl (rsOf fr) σC.slot { c1 with term := .let_ x (.atom .unit) e }

/-- **The caller's slots along a call of `print`'s argument block**: at
every entry state `σ0` of the block's invariant, the caller's control `c1`
with `x` bound to `()` before `e` placed in every slot file `sl` that agrees
with `σ0`'s off the block's fresh registers' slots (`PrintSlots` at every
state of the block, where only those slots are written; `printCallC_ofA`
gives it). -/
def PrintSlotsA (lbl : WeakMem.AllocLabel → Option Nat) (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (n : Nat) (J : AS → Ctl → Prop) (x : String) (e : Expr) (c1 : Ctl) : Prop :=
  ∀ σ0 c, J σ0 c → ∀ sl : Int → BitVec 64,
    (∀ r j, rsOf fr r = some j → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) ∧ r ≠ regName "cap" (n + 2) ∧
      r ≠ regName "k" (n + 3) → sl j = σ0.slot j) →
    SlotRepAt (fun _ => i e) lbl (rsOf fr) sl { c1 with term := .let_ x (.atom .unit) e }

/-- **The count passed to `print` below `2 ^ 63`** at every call state
(`printCallC_ofA` gives it, from the slice's length at the call site). -/
def PrintLen (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (kk : Nat) (lab : String → Int64) (pc : Int64) (n : Nat)
    (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) : Prop :=
  ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC lab fr J).J σC c →
    (σC.regs.get64 .rsi).toNat < 2 ^ 63

/-- **`PrintBlkW` with `print`'s blocks asked only under frame conditions
that know the call** (`pFJ` at `PBlk.nC`): the argument block as in
`PrintBlkW`, `print`'s blocks under every `F'` with `pFJ`, so their states
may use the caller's cells kept at the call. -/
def PrintBlkW' (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame) (B : PBlk) (J : AS → Ctl → Prop)
    (P Q : Nat → Ctl → Prop) : Prop :=
  BlkW W₀ K exe endPc R F (B.n0 fr J) B.pre ∧
    NodeW W₀ K exe endPc R F (B.nM (_root_.Executable.labels exe).label fr J) ∧
    BlkW W₀ K exe endPc R F (B.n2 (_root_.Executable.labels exe).label fr J) B.post ∧
    BlkW W₀ K exe endPc R F (B.n3 (_root_.Executable.labels exe).label fr J) [(callD, B.zc)] ∧
    ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr J).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr J) σC F' →
      PrintAW σC.regs.rbp.toBitVec (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rdi) (σC.regs.get64 .rsi).toNat
        P Q W₀ K exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F'

/-- **`PrintW` under frame conditions that know the call**: `PrintBlkW'`,
and the system call's states under every `F'` with `pFJ` at `PBlk.nC`. -/
def PrintW' (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop) (kk : Nat)
    (pc : Int64) (n : Nat)
    (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (pw wn : TermRun.Word)
    (nv mv : Nat) : Prop :=
  ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
    PrintBlkW' W₀ K exe endPc R F fr B J (PrintC pw wn nv mv) (PrintC pw wn nv mv) ∧
    ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr J).J σC c → (σC.regs.get64 .rsi).toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr J) σC F' → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      (W₀ s c' ∧ ∀ s', ¬ K s s') ∧
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1

/-- **`PrintWE` under frame conditions that know the call**: `PrintBlkW'`
at `print`'s `ret ()`. -/
def PrintWE' (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (kk : Nat) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (cE : Ctl) : Prop :=
  ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
    PrintBlkW' W₀ K exe endPc R F fr B J (fun _ c => c = cE) (fun _ _ => False)

/-- `PrintBlkW` gives `PrintBlkW'` (`pFJ` is inside `pF`). -/
theorem PrintBlkW.primed {W₀ : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {fr : Scc.Emit.X64.Frame} {B : PBlk} {J : AS → Ctl → Prop}
    {P Q : Nat → Ctl → Prop} (h : PrintBlkW W₀ K exe endPc R F fr B J P Q) :
    PrintBlkW' W₀ K exe endPc R F fr B J P Q :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun σC c hJ _ hJF => (h.2.2.2.2 σC c hJ).mono fun m hm => (hJF.2 m hm).1⟩

/-- `PrintW` gives `PrintW'`. -/
theorem PrintW.primed {W₀ : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {fr : Scc.Emit.X64.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop} {kk : Nat}
    {pc : Int64} {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {J : AS → Ctl → Prop}
    {pw wn : TermRun.Word} {nv mv : Nat} (h : PrintW W₀ K exe endPc R F ms fr Cd Bl kk pc n b o m cw J pw wn nv mv) :
    PrintW' W₀ K exe endPc R F ms fr Cd Bl kk pc n b o m cw J pw wn nv mv := fun B hB =>
  ⟨(h B hB).1.primed, fun σC c hJ hN F' hJF => (h B hB).2 σC c hJ hN F' fun md hm => (hJF.2 md hm).1⟩

/-- `PrintWE` gives `PrintWE'`. -/
theorem PrintWE.primed {W₀ : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk : Nat} {pc : Int64} {n : Nat} {b : Scc.IR.Operand}
    {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {J : AS → Ctl → Prop} {cE : Ctl}
    (h : PrintWE W₀ K exe endPc R F fr Cd Bl kk pc n b o m cw J cE) :
    PrintWE' W₀ K exe endPc R F fr Cd Bl kk pc n b o m cw J cE :=
  fun B hB => (h B hB).primed

/-- **`pFJ` at the call node with the caller's `%rbp`** gives `pFJ` at
`PBlk.nC` (the same offsets, a stronger invariant). -/
theorem PBlk.pFJ_nC {lab : String → Int64} {fr : Scc.Emit.X64.Frame} {B : PBlk} {J : AS → Ctl → Prop}
    {R : Region} {F : MachineData → Prop} {σC : AS} {F' : MachineData → Prop}
    (h : pFJ R F (B.nCR lab fr J R) σC F') : pFJ R F (B.nC lab fr J) σC F' :=
  ⟨h.1, fun m hm => by
    obtain ⟨hp, mC, c, hA, hJ, hk⟩ := h.2 m hm
    exact ⟨hp, mC, c, hA, hJ.1, hk⟩⟩

/-- **Where a call of `print` returns**: the node after the `call` at `pc'`
(`%rsp` at the frame's floor), the caller's `%rbp`; the source runs to `c2`
at the caller's frames `fs` (the return), the ghost `c0` runs to `c2`
there, and `bodyN2` holds at `c2`. -/
def printNR (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (R : Region) (fp ra : BitVec 64) (c0 : Ctl) (fs fs1 : List TermRun.Frame)
    (pc' : Int64) (e : Expr) (env' : Scc.Lower.Env) (lits' : List (String × Scc.Lower.LitV))
    (cs' bufs' : List (String × Nat)) (c2 : Ctl) : ND :=
  ⟨pc', ⟨-(fr.size : Int), []⟩, fun σ c => σ.regs.get64 .rbp = R.addr 0 ∧ FrameRun p (c, fs1) (c2, fs) ∧
    FrameRunM p (c0, fs) (c2, fs) ∧ (bodyN2 p lbl lsize i fr fp ra c2 pc' e (ofEnv2 env') lits' cs' bufs').J σ c2⟩

/-- **Where an abort of `print` lands**: `scc_rt_abort` with `%rdi = 4`
(`print_call_segW`'s abort, `%rsp` 56 bytes below the frame's floor), the
source inside `print`'s loop. -/
def printNA (lab : String → Int64) (fr : Scc.Emit.X64.Frame) : ND :=
  ⟨lab "scc_rt_abort", ⟨-(fr.size : Int) - 56, []⟩, fun σ c => σ.regs.get64 .rdi = 4 ∧
    ∃ pw wn nv mv k, PrintC pw wn nv mv k c⟩

/-- **`print`'s abort node with the caller's slots**: `printNA`, the
abstract state's slots holding the caller's control `c1` with `x` bound to
`()` before `e` (`SlotRepAt` at the table `i`): `print`'s code keeps the
caller's frame cells, so its abort lands here (`printCallC_ofA`). -/
def printNAS (lab : String → Int64) (fr : Scc.Emit.X64.Frame) (lbl : WeakMem.AllocLabel → Option Nat)
    (i : Expr → String → Nat → Option Nat) (x : String) (e : Expr) (c1 : Ctl) : ND :=
  ⟨lab "scc_rt_abort", ⟨-(fr.size : Int) - 56, []⟩, fun σ c => (printNA lab fr).J σ c ∧
    SlotRepAt (fun _ => i e) lbl (rsOf fr) σ.slot { c1 with term := .let_ x (.atom .unit) e }⟩

/-- **A state at `printNAS` is at `printNA`.** -/
theorem At.printNA_of_S {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {fr : Scc.Emit.X64.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {i : Expr → String → Nat → Option Nat}
    {x : String} {e : Expr} {c1 : Ctl} {s : State} {c : Ctl}
    (h : At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c) :
    At exe endPc R F (printNA (_root_.Executable.labels exe).label fr) s c :=
  let ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  ⟨he, hn, hdc, hpc, σ, hA, hD, hJ.1⟩

/-! ## The construct -/

section Main

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`printCallC_of'` with the caller's slots at every state of the argument
block and the count's bound** (`PrintSlotsA`, `PrintLen`, given to `hPW`,
`hPWE` besides `PrintSlots`), so the frames along the block and
`PrintCallOkR.len` need no premise per call. -/
theorem printCallC_ofA {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlotsA lbl i fr n (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 (printTop0 pw wn mv)) x e c1 →
      PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl)
      (envR : TermRun.Env) (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlotsA lbl i fr n (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs hG0 hT hfresh hLP _ hgrp _ hsh hxe hdg
    hrt hav hI hIt hIc hLb
  obtain ⟨rfl, rfl⟩ := hTp _ _ _ _ _ _ _ hT hxe
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8B hf; omega
  obtain ⟨B0, hPCC, -, hpc'⟩ := print_codeC hI
  obtain ⟨hc1, hcM, hc2, hc3⟩ := hPCC.cdOf hCd hBl
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, zs1, zs2, zM, zc, hlo1, hs1, hcap1, hk1,
    hO, hB, hL, hM, h8', hN, hC, hN', hC', hS, hKk, hz1, hz2, rfl⟩ := hPCC.toPrintCode
  let lab := (_root_.Executable.labels exe).label
  let B := pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc
  have hPC : PrintCode fr pc n b o m cw B :=
    ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, zs1, zs2, zM, zc, hlo1, hs1, hcap1, hk1,
      hO, hB, hL, hM, h8', hN, hC, hN', hC', hS, hKk, hz1, hz2, rfl⟩
  -- the block's fresh registers are off the slice's operands and each other
  have hfw : ∀ o' ∈ [b, .reg o, m, cw], ∀ r, o' = .reg r → ∀ y k, n ≤ k → r ≠ regName y k :=
    fun o' ho r hr y k hk => atomV_fresh (hfresh.mono hk) hav y o' ho r hr
  have hb : ∀ r, b = .reg r → r ≠ regName "lo" n := fun r hr => hfw b (by simp) r hr "lo" n (by omega)
  have hm : ∀ r, m = .reg r → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) := fun r hr =>
    ⟨hfw m (by simp) r hr "lo" n (by omega), hfw m (by simp) r hr "s" (n + 1) (by omega)⟩
  have hn : ∀ r, cw = .reg r → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) ∧ r ≠ regName "cap" (n + 2) :=
    fun r hr => ⟨hfw cw (by simp) r hr "lo" n (by omega), hfw cw (by simp) r hr "s" (n + 1) (by omega),
      hfw cw (by simp) r hr "cap" (n + 2) (by omega)⟩
  have hsc : regName "s" (n + 1) ≠ regName "cap" (n + 2) := Scc.Lower.Inv.regName_ne (by omega)
  have hsk : regName "s" (n + 1) ≠ regName "k" (n + 3) := Scc.Lower.Inv.regName_ne (by omega)
  have fx := fun σ0 => stC_facts hf h1 lab hlo1 hs1 hcap1 hk1 hO hB hL hM h8' hN hC hN' hC' hS hKk hb hm hn hsc hsk
    (pc := pc) (zM := zM) (zc := zc) hz1 hz2 σ0
  have hsl0 := fun σ0 fl => stC_slots hf h1 lab hlo1 hs1 hcap1 hk1 hO hB hL hM h8' hN hC hN' hC' hS hKk hb hm hn hsc
    hsk (pc := pc) (zM := zM) (zc := zc) hz1 hz2 σ0 fl
  -- the frame's cells are outside `print`'s region
  have hout : ∀ k, -(fr.size : Int) ≤ k → k % 8 = 0 → k + 8 ≤ 16 →
      R.Off k ∧ ¬ (pR (-(fr.size : Int) - 8 - 8) R).Off (k - (-(fr.size : Int) - 8 - 8)) := by
    intro k hk1 hk2 hk3
    simp only [pR, Region.Off, Region.callee]
    omega
  -- the source's names
  let t0 : Expr := .let_ x (.call "print" is a []) e
  let env' : Scc.Lower.Env := (x, .unit, []) :: env
  let lits' := (x, Scc.Lower.opLit lcx.prog lits (.call "print" is a [])) :: lits
  let cs' := Scc.Lower.csAfter x cs (.call "print" is a [])
  let bufs' := Scc.Lower.bufsAfter x cs bufs (.call "print" is a [])
  have hop : Scc.Lower.opLit lcx.prog lits (.call "print" is a []) = .nil := by
    simp only [Scc.Lower.opLit, Scc.Lower.retShape, hdg, hrt, Scc.Lower.shapeOf]
  have henv' : ofEnv2 env' = (x, .unit, []) :: ofEnv2 env := ofEnv2_cons (x := x) (env := env) rfl
  -- the code's coverage
  have hok1 := (covP_printPre hf h1 hlo1 hs1 hO hB hL hM h8').ok hz1
  have hok2 := (covP_printPost hf h1 hcap1 hk1 hN hC hN' hC' hS hKk).ok hz2
  have hne1 : B.pre ≠ [] := by
    intro h; have := congrArg List.length h; simp [B, pblk, List.length_zip, hz1, preD] at this
  have hne2 : B.post ≠ [] := by
    intro h; have := congrArg List.length h; simp [B, pblk, List.length_zip, hz2, postD] at this
  -- the entries, by the call site `c1`
  let P1 : Ctl → FragS isa := fun c1 => (At exe endPc R F ⟨pc, oB fr, fun σ c =>
      printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ ∧ LocalRun p c c1 ∧
      ((bodyN2 p lbl lsize i fr fp ra c0 pc t0 (ofEnv2 env) lits cs bufs).withTp tp).J σ c⟩).at fs
  refine (SegWS.exists_pre (P := P1) fun c1 => ?_).mono_pre ?_
  rotate_left
  · rintro s c fs' ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJ⟩, hfs⟩
    subst fs'
    obtain ⟨⟨⟨L, sm, Bm, c1, hr, hj, hl, hbB, hmB, hS⟩, hfj, hc0, -⟩, htp⟩ := id hJ
    exact ⟨c1, ⟨he, hn', hdc, hpc, σ, hA, hD, ⟨⟨L, sm, Bm, hj, hl, hbB, hmB, hS⟩, hfj, hc0.trans hr, htp⟩, hr, hJ⟩,
      rfl⟩
  by_cases hex : ∃ σ, printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ
  rotate_left
  · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, σ, _, _, hJ, _⟩, _⟩ => hex ⟨σ, hJ⟩
  obtain ⟨σx, hσx⟩ := hex
  obtain ⟨⟨Lx, smx, Bx, hjx, hlx, hBx, -⟩, -⟩ := hσx
  have hsh' : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf Scc.Frontend.ownSliceTy := by
    subst hprog; rw [hpd] at hdg; cases hdg; exact hsh
  obtain ⟨hgr, t', pw, wm, wn, mv, nv, hev, hwm, hwn, hm8⟩ :=
    printSite_of hjx hlx hBx.1 hgrp hav (hLP.1 a (by simp [headAtoms])) hsh'
  have hsa : Spike.Lib.Form.sevalAt (ofEnv2 env) a = some (t, [.loc b (.reg o), .one m, .one cw]) := by
    obtain ⟨pls, hpl, hs⟩ := sevalAt_ofEnv2L hgrp hav
    rw [hgr] at hpl; cases hpl; exact hs
  -- the length's and the count's operands at the call site
  have hval : ∀ σ0, printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ0 →
      opdVal (rsOf fr) σ0.slot m = some mv ∧ opdVal (rsOf fr) σ0.slot cw = some nv := by
    rintro σ0 ⟨⟨_, _, _, hj0, -⟩, -⟩
    obtain ⟨_, ws, hev', -, hwr⟩ := hj0.2.2.evalAt (fun _ => rfl) hsa
    rw [hev] at hev'
    simp only [Option.some.injEq, Prod.mk.injEq] at hev'
    obtain ⟨-, rfl⟩ := hev'
    obtain ⟨-, ⟨v1, hv1, hr1⟩, ⟨v2, hv2, hr2⟩, -⟩ := hwr
    rw [hwm] at hr1
    rw [hwn] at hr2
    exact ⟨hv1.trans (congrArg some hr1.2), hv2.trans (congrArg some hr2.2)⟩
  -- the frames with `print`'s, the source after the return
  let fs1 := printFrame x e c1 :: fs
  let c2 : Ctl := ⟨e, (x, .unit, []) :: c1.env, none⟩
  let N := fun _ : Unit => printNR p lbl lsize i fr R fp ra c0 fs fs1 pc' e env' lits' cs' bufs' c2
  let E := fun _ : Unit => printNAS lab fr lbl i x e c1
  -- the return lands at `N`
  have landR : ∀ σ0 fl, printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ0 →
      (B.stC lab fr σ0 fl).regs.get64 .rbp = R.addr 0 → ∀ σR c',
      σR.regs.get64 .rbp = (B.stC lab fr σ0 fl).regs.rbp.toBitVec → FrameRun p (c', fs1) (c2, fs) →
      (∀ k, R.Off k → ¬ (pR (-(fr.size : Int) - 8 - 8) R).Off (k - (-(fr.size : Int) - 8 - 8)) →
        σR.slot k = (B.stC lab fr σ0 fl).slot k) →
      Hit (N ()) ⟨Int64.ofBitVec ((B.stC lab fr σ0 fl).slot (-(fr.size : Int) - 8)),
        ⟨-(fr.size : Int) - 8 + 8, []⟩, σR⟩ c' := by
    intro σ0 fl hJL hbp σR c' hrbp hrun hsl
    obtain ⟨⟨L, sm, Bm, hj, hl, hbB, hmB, hS⟩, hfj, hc0, -⟩ := hJL
    obtain ⟨_, _, _, _, -, -, -, -, -, hrest⟩ := fx σ0
    obtain ⟨-, -, -, hra, -⟩ := hrest fl
    -- a cell of the frame is kept from the block's entry
    have hkeep : ∀ k, -(fr.size : Int) ≤ k → k % 8 = 0 → k + 8 ≤ 16 →
        (∀ q, rsOf fr q = some k → q ≠ regName "lo" n ∧ q ≠ regName "s" (n + 1) ∧ q ≠ regName "cap" (n + 2) ∧
          q ≠ regName "k" (n + 3)) → σR.slot k = σ0.slot k := by
      intro k hk1 hk2 hk3 hq
      obtain ⟨ho1, ho2⟩ := hout k hk1 hk2 hk3
      rw [hsl k ho1 ho2]
      exact hsl0 σ0 fl k (by omega) hq
    have hnone : ∀ k, 0 ≤ k → ∀ q, rsOf fr q = some k → q ≠ regName "lo" n ∧ q ≠ regName "s" (n + 1) ∧
        q ≠ regName "cap" (n + 2) ∧ q ≠ regName "k" (n + 3) := by
      intro k hk q hq; have := (rsOf_bounds hf hq).1; omega
    have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
        opdVal (rsOf fr) σR.slot o' = opdVal (rsOf fr) σ0.slot o' := by
      intro q hq pl hpl o' ho'
      refine opdVal_upd fun r k hor hr => ?_
      obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hr
      refine hkeep k (by omega) hk2 (by omega) fun q' hq' => ?_
      have hqr := rsOf_inj hf hq' hr
      subst hqr
      exact ⟨Fresh.ofEnv2 hfresh "lo" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 1)) "s" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 2)) "cap" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 3)) "k" q hq pl hpl o' ho' _ hor⟩
    have hjE := NodeJE.unitBind hj hsl'
    refine ⟨?_, ?_, hbp ▸ hrbp, hrun, (FrameRunM.ofLocal hc0 fs).trans (FrameRunM.mem1 hj.2.1 hj.1 rfl),
      ⟨L, sm, Bm, ?_⟩, ?_, .refl _, ?_⟩
    · show pc' = Int64.ofBitVec _
      rw [hra, Int64.ofBitVec_toBitVec, hpc']; rfl
    · simp only [SO.le, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by simp [N, printNR], rfl⟩
    · show NJB p lbl (rsOf fr) ((x, Scc.Lower.opLit lcx.prog lits (.call "print" is a [])) :: lits) cs' bufs' L sm
        lsize Bm
        e (ofEnv2 env') σR.slot c2
      rw [henv', hop]
      exact NJB.printUnit hj hl hbB hmB hS hsl'
    · exact ⟨(hkeep 0 (by omega) (by decide) (by decide) (hnone 0 (Int.le_refl 0))).trans hfj.1,
        (hkeep 8 (by omega) (by decide) (by decide) (hnone 8 (by decide))).trans hfj.2⟩
    · refine SlotRepAt.of_nodeJE hjE ?_ ?_ ?_
      · rw [← henv']; exact hIt
      · rw [← henv']; exact hLb
      · rw [← henv']; exact hIc
  -- the caller's slots at the call states
  have hcons : ∀ y, y ≠ x → lookupS (ofEnv2 env') y = lookupS (ofEnv2 env) y := by
    intro y hy
    rw [henv']
    simp [lookupS, List.find?_cons, Ne.symm hy]
  have hfv : ∀ y ∈ Scc.Sem.exprFv (Expr.let_ x (.atom .unit) e), y ∈ Scc.Sem.exprFv e ∧ y ≠ x := by
    intro y hy
    simpa [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars] using hy
  have hslotsA : ∀ cE, PrintSlotsA lbl i fr n (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) x e c1 := by
    intro cE σ0 c hc sl hsl
    obtain ⟨-, hJL⟩ := hc
    obtain ⟨⟨_, _, _, hj, -⟩, -⟩ := hJL
    have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
        opdVal (rsOf fr) sl o' = opdVal (rsOf fr) σ0.slot o' := by
      intro q hq pl hpl o' ho'
      refine opdVal_upd fun r k hor hr => ?_
      exact hsl r k hr ⟨Fresh.ofEnv2 hfresh "lo" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 1)) "s" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 2)) "cap" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 3)) "k" q hq pl hpl o' ho' _ hor⟩
    have hs := hj.2.2.congr hsl'
    refine SlotRepAt.of_srepE (s := (ofEnv2 env).filter (·.1 != x)) ?_ ?_ ?_ ?_
    · intro y ty' pls hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact hs y ty' pls hl
    · intro y hy
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2, ← hcons y hy.2]
      exact hIt y hy.1
    · intro y hy ty' pls hl b' o' hb'
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2, ← hcons y hy.2] at hl
      exact hLb y hy.1 ty' pls hl b' o' hb'
    · intro y k v hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy, ← hcons y hy] at hl
        exact hIc y k v hl
  have hslots : ∀ cE, PrintSlots lbl i fr Cd Bl kk lab pc n b o m cw
      (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) x e c1 := by
    intro cE B' hB' σC c hc
    obtain ⟨olo', os', ocap', okk', lO', lB', lL', lM', l8', lN', lC', lN'', lC'', lS', lK', zs1', zs2', zM', zc',
      hlo1', hs1', hcap1', hk1', hO', hB'', hL', hM', h8'', hN'', hC'', hN''', hC''', hS', hKk', hz1', hz2', rfl⟩ :=
      hB'.toPrintCode
    obtain ⟨σ0, fl, hJ0, hσ⟩ := hc
    refine hslotsA cE σ0 c hJ0 σC.slot fun r k hr hne => ?_
    obtain ⟨-, -, hk3⟩ := rsOf_bounds hf hr
    rw [hσ]
    refine stC_slots hf h1 lab hlo1' hs1' hcap1' hk1' hO' hB'' hL' hM' h8'' hN'' hC'' hN''' hC''' hS' hKk' hb hm hn
      hsc hsk (pc := pc) (zM := zM') (zc := zc') hz1' hz2' σ0 fl k (by omega) fun q' hq' => ?_
    have hqr := rsOf_inj hf hq' hr
    subst hqr
    exact hne
  have hlenA : ∀ cE, PrintLen fr Cd Bl kk lab pc n b o m cw
      (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) := by
    intro cE B' hB' σC c hc
    obtain ⟨olo', os', ocap', okk', lO', lB', lL', lM', l8', lN', lC', lN'', lC'', lS', lK', zs1', zs2', zM', zc',
      hlo1', hs1', hcap1', hk1', hO', hB'', hL', hM', h8'', hN'', hC'', hN''', hC''', hS', hKk', hz1', hz2', rfl⟩ :=
      hB'.toPrintCode
    obtain ⟨σ0, fl, ⟨-, hJL⟩, rfl⟩ := hc
    obtain ⟨vb, vo, vm, vn, -, -, hvm, -, -, hrest⟩ := stC_facts hf h1 lab hlo1' hs1' hcap1' hk1' hO' hB'' hL' hM'
      h8'' hN'' hC'' hN''' hC''' hS' hKk' hb hm hn hsc hsk (pc := pc) (zM := zM') (zc := zc') hz1' hz2' σ0
    obtain ⟨-, -, hsi, -, -⟩ := hrest fl
    have hm' := (hval σ0 hJL).1
    rw [hvm] at hm'
    have em : vm.toNat = mv := Option.some.inj hm'
    have h8m : (vm * 8#64).toNat = mv * 8 := by
      rw [BitVec.toNat_mul, em]; simp only [BitVec.toNat_ofNat]; omega
    rw [hsi]
    split
    · omega
    · rw [h8m]; omega
  -- the frames: the call taken at the entry, the return at the exit
  have plumb : ∀ cE : Ctl, FrameRun p (c1, fs) (cE, fs1) →
      SegW (fun s c => W s c fs1) K p lbl (ms fs1)
        (At exe endPc R F (B.n0 fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE)))
        (fun s c => Next exe endPc R F N E s c ∧ TP tp s) →
      SegWS W K p lbl ms (P1 c1) (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e env' lits' cs' bufs') :=
        by
    intro cE hrun hseg
    refine SegWS.post_run ((SegWS.pre_run (P := P1 c1) (SegWS.liftS fs1 hseg fun _ _ h => h) ?_).mono_post ?_)
    · rintro s c fs' ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJL, hr, hJ⟩, hfs⟩
      subst fs'
      exact ⟨hWL c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 hT hI
        ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJ⟩, rfl⟩, cE, fs1,
        (FrameRun.ofLocal hr fs).trans hrun, ⟨he, hn', hdc, hpc, σ, hA, hD, rfl, hJL⟩, rfl⟩
    · rintro s c fs' ⟨⟨⟨_, he, hn', hdc, hpc, σ, hA, hD, hbp, hrun2, hgh, hJ2⟩ | ⟨_, hat⟩, htp⟩, hfs⟩ <;> subst fs'
      · refine ⟨c2, fs, hrun2, .inl ⟨rfl, c2, hgh, ?_⟩⟩
        have hat : At exe endPc R F ⟨pc', ⟨-(fr.size : Int), []⟩, fun σ' _ => σ'.regs.get64 .rbp = R.addr 0 ∧
            (bodyN2 p lbl lsize i fr fp ra c2 pc' e (ofEnv2 env') lits' cs' bufs').J σ' c2 ∧ σ'.regs.fsBase = tp⟩ s
              c2 :=
          ⟨he, hn', hdc, hpc, σ, hA, hD, hbp, hJ2, by rw [← hA.regs]; exact htp⟩
        obtain ⟨he', hn'', hdc', hpA, σ', hA', hD', -, hJ', htp'⟩ := at_rbp_addr (k := 0) hat fun _ _ h => h.1
        exact ⟨he', hn'', hdc', hpA, σ', hA', hD', hJ', htp'⟩
      · exact ⟨c, fs1, .refl _, .inr (hAb c0 x is a e c1 s c hG0 hT hat)⟩
  -- the block and the `call`, the `%fs` base kept
  have mkS1 : ∀ (cE : Ctl) (P Q : Nat → Ctl → Prop),
      PrintBlkW' (fun s c => W s c fs1) K exe endPc R F fr B
        (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE)
        P Q →
      SegW (fun s c => W s c fs1) K p lbl (ms fs1)
        (At exe endPc R F (B.n0 fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE)))
        (fun s c => At exe endPc R F (B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) R) s c
          ∧
          TP tp s) := by
    rintro cE P Q ⟨hW1, hWM, hW2, hW3, _⟩
    refine (print_blocks_toC h8 (lo := -(fr.size : Int)) (hi := 16) hne1 hne2 hok1 hok2 hc1 hcM hc2 hc3 hW1 hWM hW2
      hW3 (fun σ0 _ _ => by obtain ⟨_, _, _, _, _, _, _, _, hr, _⟩ := fx σ0; exact hr) rfl
      (fun σ0 _ fl _ => by obtain ⟨_, _, _, _, _, _, _, _, _, hr⟩ := fx σ0; exact (hr fl).1) hF hR (by omega) hhi
      (by omega) (by omega)).mono_post fun s c h => ⟨h, ?_⟩
    obtain ⟨-, -, -, -, σ, hA, -, ⟨σ0, fl, ⟨-, hJL⟩, hσ⟩, -⟩ := h
    show s.st.1.regs.fsBase = tp
    rw [hA.regs, hσ, stC_fsBase]
    exact hJL.2.2.2
  by_cases hm0 : mv = 0
  · -- an empty slice: `print`'s body to `ret ()`
    obtain ⟨envR, hrunE⟩ := printCall_emptyR (fs := fs) hpd hjx.1 hev (by rw [hwm, hm0])
    let cE : Ctl := ⟨.ret .unit, envR, none⟩
    refine plumb cE hrunE ?_
    have hBW := hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI (hslotsA _) (hlenA _) (hslots _) B hPCC
    refine (mkS1 cE _ _ hBW).seq ?_
    refine print_call_emptyW_tp' (nC := B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) R)
      (Pe := fun _ c => c = cE) hp hend hpin hF hR (by show R.lo ≤ -(fr.size : Int) - 8 - 8 + -40; omega)
      (by show -(fr.size : Int) - 8 - 8 + 16 ≤ R.hi; omega) (by show (-(fr.size : Int) - 8 - 8) % 8 = 0; omega) rfl
      (fun σ c ⟨⟨σ0, fl, ⟨hc, _⟩, _⟩, _⟩ => hc) ?_
      (fun σC c h F' hJF => hBW.2.2.2.2 σC c h.1 F' (PBlk.pFJ_nC hJF)) (hK fs1) ?_
    · rintro σ c ⟨⟨σ0, fl, ⟨-, hJL⟩, rfl⟩, -⟩
      obtain ⟨vb, vo, vm, vn, -, -, hvm, -, -, hrest⟩ := fx σ0
      obtain ⟨-, -, hsi, -, -⟩ := hrest fl
      have hvm' : vm.toNat = 0 := by
        have := (hval σ0 hJL).1; rw [hvm, hm0] at this; exact Option.some.inj this
      have hv0 : vm = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hvm')
      rw [hsi, hv0]
      simp
    · rintro σC c σR c' ⟨⟨σ0, fl, ⟨-, hJL⟩, rfl⟩, hbp⟩ hrbp hc' hsl
      subst hc'
      exact .inl ⟨(), landR σ0 fl hJL hbp σR _ hrbp (.single (printCall_ret rfl)) hsl⟩
  · -- a nonempty slice: `print`'s loop
    have hen := printCall_enter (p := p) (fs := fs) hpd hd hjx.1 hev hwm hm0 hwn
    refine plumb _ hen.1 ?_
    -- the buffer word the start of a location placed at `%rdi`
    have hpwX : ∀ B', PrintCodeC fr Cd Bl kk pc n b o m cw B' → ∀ σC c, (B'.nC lab fr
        (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat := by
      intro B' hB' σC c hc
      obtain ⟨olo', os', ocap', okk', lO', lB', lL', lM', l8', lN', lC', lN'', lC'', lS', lK', zs1', zs2', zM', zc',
        hlo1', hs1', hcap1', hk1', hO', hB'', hL', hM', h8'', hN'', hC'', hN''', hC''', hS', hKk', hz1', hz2', rfl⟩ :=
        hB'.toPrintCode
      obtain ⟨σ0, fl, ⟨-, hJL⟩, rfl⟩ := hc
      obtain ⟨l, -, hpw0, -, -⟩ := print_arg_slAt hBx.1 hev hsh'
      obtain ⟨vb, vo, _vm, _vn, hvb, hvo, _, _, _, hrest⟩ := stC_facts hf h1 lab hlo1' hs1' hcap1' hk1' hO' hB'' hL' hM'
        h8'' hN'' hC'' hN''' hC''' hS' hKk' hb hm hn hsc hsk (pc := pc) (zM := zM') (zc := zc') hz1' hz2' σ0
      obtain ⟨-, hx0, -⟩ := hrest fl
      obtain ⟨⟨_, _, _, hj0, -⟩, -⟩ := hJL
      obtain ⟨_, ws, hev', -, hwr⟩ := hj0.2.2.evalAt (fun _ => rfl) hsa
      rw [hev] at hev'
      simp only [Option.some.injEq, Prod.mk.injEq] at hev'
      obtain ⟨-, rfl⟩ := hev'
      obtain ⟨⟨vb', vo', hb', ho', hloc⟩, -⟩ := hwr
      rw [hpw0] at hloc
      obtain ⟨-, hl', hoff⟩ := hloc
      rw [hvb] at hb'
      rw [hvo] at ho'
      have e1 : vb.toNat = vb' := Option.some.inj hb'
      have e2 : vo.toNat = vo' := Option.some.inj ho'
      have ho0 : vo' = 0 := by simpa using hoff
      have hv0 : vo = 0#64 := BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
      refine ⟨l, hpw0, ?_⟩
      rw [hx0, hv0]
      simpa [BitVec.take, e1] using hl'
    obtain ⟨hBW, hsys⟩ :=
      hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpwX (hslotsA _) (hlenA _) (hslots _) B hPCC
    refine (mkS1 _ _ _ hBW).seq ?_
    -- the count passed to `print`
    have hcnt : ∀ σ c,
      (B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv)) R).J
        σ c → (σ.regs.get64 .rsi).toNat = printN nv mv := by
      rintro σ c ⟨⟨σ0, fl, ⟨-, hJL⟩, hσ⟩, -⟩
      subst hσ
      obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, hrest⟩ := fx σ0
      obtain ⟨-, -, hsi, -, -⟩ := hrest fl
      obtain ⟨hm', hn'⟩ := hval σ0 hJL
      rw [hvm] at hm'
      rw [hvn] at hn'
      have em : vm.toNat = mv := Option.some.inj hm'
      have en : vn.toNat = nv := Option.some.inj hn'
      rw [hsi, printN_of_rsi (by rw [em]; exact hm8), em, en]
    refine print_call_segW_tp' (nC := B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1
        (printTop0 pw wn mv)) R) (N := N) (E := E) (pw := fun _ => pw) (wn := fun _ => wn) (n := fun _ => nv)
      (m := fun _ => mv) hp hend hpin hF hR (by show R.lo ≤ -(fr.size : Int) - 8 - 8 + -40; omega)
      (by show -(fr.size : Int) - 8 - 8 + 16 ≤ R.hi; omega) (by show (-(fr.size : Int) - 8 - 8) % 8 = 0; omega) rfl
      (fun σ c ⟨⟨σ0, fl, ⟨hc, _⟩, _⟩, _⟩ => hc ▸ hen.2) hcnt (fun _ _ _ => hm8)
      (fun σC c h F' hJF => hBW.2.2.2.2 σC c h.1 F' (PBlk.pFJ_nC hJF)) hd (hK fs1) (hcl fs1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h.1 (hcnt σC c h) F' (PBlk.pFJ_nC hJF) s c' hAt).1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h.1 (hcnt σC c h) F' (PBlk.pFJ_nC hJF) s c' hAt).2.1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h.1 (hcnt σC c h) F' (PBlk.pFJ_nC hJF) s c' hAt).2.2) ?_ ?_
    · rintro σC c σR c' ⟨⟨σ0, fl, ⟨-, hJL⟩, rfl⟩, hbp⟩ hrbp hc' hsl
      exact .inl ⟨(), landR σ0 fl hJL hbp σR c' hrbp (printCall_exit hc') hsl⟩
    · rintro σC c σR c' k ⟨⟨σ0, fl, hJ0, rfl⟩, -⟩ hrdi hc' hkS
      refine .inr ⟨(), rfl, ?_, ⟨hrdi, pw, wn, nv, mv, k, hc'⟩, hslotsA _ σ0 c hJ0 σR.slot fun r j hr hne => ?_⟩
      · show SO.le ⟨-(fr.size : Int) - 56, []⟩ ⟨-(fr.size : Int) - 8 - 8 + -40, []⟩ = true
        simp only [SO.le]; simp; omega
      · -- the caller's slots kept from the call (off `print`'s region), there off the block's fresh registers
        obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hr
        obtain ⟨ho1, ho2⟩ := hout j (by omega) hk2 (by omega)
        rw [hkS j ho1 ho2]
        exact hsl0 σ0 fl j (by omega) fun q' hq' => by rw [rsOf_inj hf hq' hr]; exact hne

/-- **`printCallC_of` with `print`'s states asked only under frame
conditions that know the call** (`PrintW'`, `PrintWE'`: `pFJ` at
`PBlk.nC`, through `print_call_segW_tp'`, `print_call_emptyW_tp'`), given
the caller's slots at the call states (`PrintSlots`), so they may use the
caller's cells kept at the call (e.g. the frames placed). -/
theorem printCallC_of' {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl)
      (envR : TermRun.Env) (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallC_ofA hf h1 hF hR hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw _ _ hS =>
      hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw hS)
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI _ _ hS =>
      hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI hS) hAb

/-- **An output call of an `Accepted2` body** (`PrintCallC`), in the
frame's region (`hlo`, `hhi`) of a layout with `scc_rt_print` (`printIn`):
the code predicates give code (`hCd`, `hBl`); the externs called are
`print` with no type arguments (`hTp`), the call's program `p` (`hprog`;
at the call site the slice's words a locative, its length and the count by
`printSite_of`); the states at the `let` (`hWL`), along the argument block and in `print` (`PrintW`,
`PrintWE` at `printJ`, inside `W` at `print`'s frames, given the block's
code `InstsC2`) lie in `W`; an abort of `print` is one of `Ab` (`hAb`). -/
theorem printCallC_of {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintW (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl)
      (envR : TermRun.Env) (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintWE (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallC_of' hf h1 hF hR hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw _ =>
      (hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw).primed)
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI _ =>
      (hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI).primed) hAb

end Main

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.print_blocks_toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.print_blocks_toC

/-- info: 'Spike.Lib.LowerX64.printCallC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_of

/-- info: 'Spike.Lib.LowerX64.printCallC_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_of'

/-- info: 'Spike.Lib.LowerX64.At.printNA_of_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.At.printNA_of_S

/-- info: 'Spike.Lib.LowerX64.PrintW.primed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.PrintW.primed

/-- info: 'Spike.Lib.LowerX64.printCallC_ofA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_ofA
