/-
**A buffer allocation's premise** (x86-64): `NewBufC` (`Body2.lean`) from
`newBuf_blkW` (`Spike/Lib/X64NewBuf.lean`, the allocator's `callq` after the
argument loads), the source's allocation at any label by a ghost memory
(`EnvB.newBufG`, `Spike/Lib/Src/EnvBGhost.lean`) and the store of the
returned base into `x%n`'s slot. The x86-64 twin of
`Spike/Lib/LowerA64/NewBufC2.lean`.

- `instsC2_newBuf`: `InstsC2`'s allocation arm;
- `getOps_three`, `args3_step`, `okBlk_args3`, `args3_ne_nil`: the
  arguments' loads into `%rdi`, `%rsi`, `%rdx`;
- `nbJ1`: the call's source relation after the argument loads;
- `nbL`, `nbJS`: the states at the landing after the allocator's return on
  either route, and with the facts the store asks for;
- `AllocW2`: the memory side's states at one allocation's caller blocks in
  `W₀` (indexed by the placement, the returned base's store at any
  placement extending the call's) and the allocator's premises (`newBuf_blkW`'s `hq`, `hmem`, `hxa`,
  `hW`) at that call's node (`nbJc`), per use (`LaneW`'s style);
- `nbArgs_seg`, `nbCall_seg`, `nbStore_seg`, `nbRet_seg`: the segments;
- `htot_newBuf`, `nbJ1_upd_out`, `NbJcOf`, `nbJcOf_nbJ1`: the free variables
  at an allocation bound; its call node's controls placed in the slot file
  at a `newBuf` of an `elem2` type (`newBufC_of`'s `hAb` premise, so that
  the heap abort's stub may place them; the `callq`'s push is below the
  frame); `nbJc_nbJ1_term`: its controls at the allocation's term (so at
  the walk predicate, `hAb`'s other premise);
- `newBufC_of`: the premise.

Where x86-64 differs from AArch64: the return address is pushed at
`-size - 8` (the allocator's region `R.callee (-size - 8) (-160) 8`); the
thread pointer is the `%fs` base (`NoSetFsW`, `SegW.keepTPN` of
`Spike/Lib/X64Hello1RodataTP.lean`); the frame's slots are `%rbp`-relative,
so the call's source relation carries `%rbp = R.addr 0` (`nbJ1`) for the
landing's store.
-/
import Spike.Lib.LowerX64.LaneC2
import Spike.Lib.LowerX64.CallC2
import Spike.Lib.X64NewBuf
import Spike.Lib.X64Hello1RodataTP
import Spike.Lib.Src.NJBNewBuf
import Spike.Lib.Src.NodeJEMono

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (Item i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJE lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName atomV)
open Scc.Sem (ValRep)
open Spike.Lib.LowerShape (newBufCall newBufTy unitsOf)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW Ea)
open Spike.Lib.X64.Flow.NewBuf (nbJc nbX AllocCtx allocAbortDepth allocFrame newBuf_blkW)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Scc.Cert.Rt.X64 (Lays endOf)

set_option linter.unusedSimpArgs false

/-! ## The code -/

section Code

variable {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
  {Bl : Int64 → Nat → Label → Nat → Prop}

/-- **`InstsC2`'s allocation arm**: the arguments' loads at `pc`, `callq
scc_rt_alloc` after them (`Bl`), the returned base's store; the counter and
the pc after it. -/
theorem instsC2_newBuf {k k' : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {h : Nat} {kv : UInt64}
    {u : Scc.IR.Operand} (hi : InstsC2 fr Cd Bl k pc [newBufCall d h kv u] k' pc') :
    ∃ lw off zs zc z, getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw ∧
      rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧ k' = k + 1 ∧
      pc' = pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z := by
  rcases hi with ⟨hc, -⟩ | ⟨_, _, _, _, _, _, _, _, he, -⟩ |
      ⟨d', ws, lw, off, zs, zc, z, he, -, hl, ho, hz, h1, h2, h3, ⟨hk, hp⟩⟩ | ⟨_, _, _, _, he, -⟩
  · simp [Spike.Lib.LowerShape.isCall, newBufCall] at hc
  · simp [newBufCall] at he
  · simp only [newBufCall, Scc.IR.Inst.call.injEq, List.cons.injEq, and_true, true_and] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨lw, off, zs, zc, z, hl, ho, hz, h1, h2, h3, hk, hp⟩
  · simp [newBufCall] at he

/-- **The call's three argument loads**: `a` into `%rdi`, `b` into `%rsi`,
`c` into `%rdx`. -/
theorem getOps_three {a b c : Scc.IR.Operand} {lw : List Item}
    (h : getOps fr ([a, b, c].zip Scc.Emit.X64.argRegs) = .ok lw) :
    ∃ la lb lc, getOp fr .rdi a = .ok la ∧ getOp fr .rsi b = .ok lb ∧ getOp fr .rdx c = .ok lc ∧
      lw = la ++ lb ++ lc := by
  simp only [Scc.Emit.X64.argRegs, List.zip_cons_cons, List.zip_nil_left, getOps] at h
  cases ha : getOp fr .rdi a with
  | error e => simp [ha] at h
  | ok la =>
    cases hb : getOp fr .rsi b with
    | error e => simp [ha, hb] at h
    | ok lb =>
      cases hc : getOp fr .rdx c with
      | error e => simp [ha, hb, hc] at h
      | ok lc =>
        simp only [ha, hb, hc] at h
        cases h
        exact ⟨la, lb, lc, rfl, rfl, rfl, by simp⟩

/-- The three loads' cells, one per load. -/
theorem args3_split {a b c : Scc.IR.Operand} {la lb lc : List Item} (ha : getOp fr .rdi a = .ok la)
    (hb : getOp fr .rsi b = .ok lb) (hc : getOp fr .rdx c = .ok lc) {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ lc)).length) :
    ∃ z1 z2 z3, zs = [z1, z2, z3] ∧ [z1].length = (dirs la).length ∧ [z2].length = (dirs lb).length ∧
      [z3].length = (dirs lc).length ∧
      (dirs (la ++ lb ++ lc)).zip zs = (dirs la).zip [z1] ++ (dirs lb).zip [z2] ++ (dirs lc).zip [z3] := by
  obtain ⟨da, eA⟩ := dirs_getOp ha
  obtain ⟨db, eB⟩ := dirs_getOp hb
  obtain ⟨dc, eC⟩ := dirs_getOp hc
  rw [dirs_append, dirs_append, eA, eB, eC] at hz ⊢
  match zs, hz with
  | [z1, z2, z3], _ => exact ⟨z1, z2, z3, rfl, rfl, rfl, rfl, rfl⟩

/-- **The loads of three arguments** into `%rdi`, `%rsi`, `%rdx`: the
slots, `%rbp` and the `%fs` base unchanged. -/
theorem args3_step (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {a b c : Scc.IR.Operand} {lw : List Item}
    (h : getOps fr ([a, b, c].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) (lab : String → Int64) (pc : Int64) (σ : AS) :
    ∃ va vb vc : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧
      opdVal (rsOf fr) σ.slot b = some vb.toNat ∧ opdVal (rsOf fr) σ.slot c = some vc.toNat ∧
      ∃ rg : Reg64s, rg.get64 .rdi = va ∧ rg.get64 .rsi = vb ∧ rg.get64 .rdx = vc ∧
        rg.fsBase = σ.regs.fsBase ∧ rg.get64 .rbp = σ.regs.get64 .rbp ∧
      arun lab ((dirs lw).zip zs) ⟨pc, oB fr, σ⟩ = ⟨pc + Int64.ofNat zs.sum, oB fr, { σ with regs := rg }⟩ := by
  obtain ⟨la, lb, lc, ha, hb, hc, rfl⟩ := getOps_three h
  obtain ⟨z1, z2, z3, rfl, hz1, hz2, hz3, hsp⟩ := args3_split ha hb hc hz
  obtain ⟨va, hva, ra⟩ := arun_getOp hf h1 (by decide) ha lab pc σ hz1
  obtain ⟨vb, hvb, rb⟩ := arun_getOp hf h1 (by decide) hb lab (pc + Int64.ofNat [z1].sum)
    { σ with regs := σ.regs.set64 .rdi va } hz2
  obtain ⟨vc, hvc, rc⟩ := arun_getOp hf h1 (by decide) hc lab (pc + Int64.ofNat [z1].sum + Int64.ofNat [z2].sum)
    { σ with regs := (σ.regs.set64 .rdi va).set64 .rsi vb } hz3
  refine ⟨va, vb, vc, hva, hvb, hvc, ((σ.regs.set64 .rdi va).set64 .rsi vb).set64 .rdx vc,
    by simp [Reg64s.get64_set64], by simp [Reg64s.get64_set64], by simp [Reg64s.get64_set64],
    by simp [Reg64s.set64_fsBase], by simp [Reg64s.get64_set64], ?_⟩
  rw [hsp, arun_append, arun_append, ra, rb, rc]
  simp [List.sum_cons, Int64.ofNat_add, Int64.add_assoc]

/-- **The loads of three arguments are covered.** -/
theorem okBlk_args3 (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {a b c : Scc.IR.Operand} {lw : List Item}
    (h : getOps fr ([a, b, c].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs lw).zip zs) = true := by
  obtain ⟨la, lb, lc, ha, hb, hc, rfl⟩ := getOps_three h
  obtain ⟨z1, z2, z3, rfl, hz1, hz2, hz3, hsp⟩ := args3_split ha hb hc hz
  have e3 := okBlk_getOp hf h1 (by decide) (by decide) hc hz3 []
  rw [List.append_nil] at e3
  rw [hsp, List.append_assoc, okBlk_getOp hf h1 (by decide) (by decide) ha hz1,
    okBlk_getOp hf h1 (by decide) (by decide) hb hz2, e3]
  rfl

/-- **The loads of three arguments are not empty.** -/
theorem args3_ne_nil {a b c : Scc.IR.Operand} {lw : List Item}
    (h : getOps fr ([a, b, c].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) : (dirs lw).zip zs ≠ [] := by
  obtain ⟨la, lb, lc, ha, hb, hc, rfl⟩ := getOps_three h
  obtain ⟨z1, z2, z3, rfl, hz1, hz2, hz3, hsp⟩ := args3_split ha hb hc hz
  obtain ⟨da, eA⟩ := dirs_getOp ha
  rw [hsp, eA]
  simp

end Code

/-! ## The call's nodes -/

/-- **The call's source relation after the argument loads** (`newBuf_blkW`'s
`J1`): the operands `a0`, `a1`, `a2` valued in `%rdi`, `%rsi`, `%rdx`, the
saved pair, the `%fs` base `tp`, `%rbp` at the frame record, the source at
the allocation itself (`c1`, reached from the ghost `c0`) with the node's
invariant up to the buffers' literal lengths at `t` and the environment's
literal, buffer and size facts. -/
def nbJ1 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (fr : Scc.Emit.X64.Frame) (R : Region) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (t : Expr)
    (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (a0 a1 a2 : Scc.IR.Operand) : AS → Ctl → Prop :=
  fun σ c1 => opdVal (rsOf fr) σ.slot a0 = some (σ.regs.get64 .rdi).toNat ∧
    opdVal (rsOf fr) σ.slot a1 = some (σ.regs.get64 .rsi).toNat ∧
    opdVal (rsOf fr) σ.slot a2 = some (σ.regs.get64 .rdx).toNat ∧
    FrJ fp ra σ.slot ∧ σ.regs.fsBase = tp ∧ σ.regs.get64 .rbp = R.addr 0 ∧ LocalRun p c0 c1 ∧
    ∃ L sm B, NodeJE lbl (rsOf fr) t (ofEnv2 env) σ.slot c1 ∧ EnvLit lits c1.env ∧
      EnvB lits cs bufs L sm lsize c1.env ∧ MemB L sm B ∧ EnvSmall c1.env

/-- **The states after the allocator's return at the landing**, on either
route (the `.ret` exit, or a fresh label's continuation): some call whose
source control a state of the call node `Jc` had, the caller's cells
outside the allocator's region as there, the source past its allocation at
some label, `%rax` the base for the counter's old value. -/
def nbL (ms : MemSide isa) (L : Label → Int64) (R : Region) (fs : Int) (Jc : AS → Ctl → Prop) :
    AS → Ctl → Prop :=
  fun σ c => ∃ q : {q : Call // q.OK ms L},
    (∃ σC, Jc σC q.1.c0 ∧
      ∀ k, R.Off k → ¬ (R.callee (-fs - 8) (-160) 8).Off (k - (-fs - 8)) → σ.slot k = σC.slot k) ∧
    ∃ (l : WeakMem.AllocLabel) (ini old : Nat), c = allocCtl q.1.c0 q.1.x q.1.τ q.1.e q.1.n l ini ∧
      σ.regs.rax.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧ old + ms.units q.1.n q.1.τ ≤ ms.cells

/-- **The landing's facts for the store** at the label map `lbl'` and sizes
`lsize'`: `nbL`'s, the returned label's locative represented by `%rax` at
`lbl'` and holding the count at `lsize'`, the `%fs` base `tp`. -/
def nbJS (ms : MemSide isa) (L : Label → Int64) (lbl' : WeakMem.AllocLabel → Option Nat)
    (lsize' : WeakMem.AllocLabel → Nat) (R : Region) (fs : Int) (tp : UInt64) (Jc : AS → Ctl → Prop) :
    AS → Ctl → Prop :=
  fun σ c => ∃ q : {q : Call // q.OK ms L},
    (∃ σC, Jc σC q.1.c0 ∧
      ∀ k, R.Off k → ¬ (R.callee (-fs - 8) (-160) 8).Off (k - (-fs - 8)) → σ.slot k = σC.slot k) ∧
    ∃ (l : WeakMem.AllocLabel) (ini old : Nat), c = allocCtl q.1.c0 q.1.x q.1.τ q.1.e q.1.n l ini ∧
      σ.regs.rax.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧ old + ms.units q.1.n q.1.τ ≤ ms.cells ∧
      ValRep lbl' (.loc ⟨l, 0⟩ 0) σ.regs.rax.toNat ∧ q.1.n ≤ lsize' l ∧ σ.regs.fsBase = tp

/-! ## The memory side's premise -/

/-- **The memory side's states at one allocation's caller blocks in `W₀`
and the allocator's premises**, for the call's code at `Cd`, `Bl` (the
arguments' loads `lw` into `%rdi`, `%rsi`, `%rdx` from `pc` with cells `zs`,
`callq scc_rt_alloc` at `pcB` after them, the returned base's store into
`d`'s slot `off` at the landing `pcR`): the states along the loads from
`⟨pc, oB fr, J⟩` and at the `callq` from `J1` lie in `W₀` at the placement
`lbl`, `lsize`; at the store from the landing at any placement `lbl'`,
`lsize'` extending it (`nbJS`, the returned label placed at `%rax` and
holding the count: `lbl` itself on the `.ret` route, the fresh label added
on the other) in `W₀` at `lbl'`, `lsize'`; at the call's node
(`nbJc` of the `callq` from `J1`): each state's arguments are some call's
with its premises (`hq`), the counter and every header the call may store
are unmapped under `F` (`hmem`), a fresh label's allocation at the `%fs`
base `tp` lands in `ms.xa` (`hxa`), and the allocator's states for every
such call returning to `pcR` are inside `W₀` at `fsBase = tp` in the call's
context (`hW`; the call keeps `tp`, so no other state is asked);
a label already placed at the allocation's base holds its count (`hsz`, the
sizes `lsize`). -/
def AllocW2 (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isa)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (tp : UInt64) (fr : Scc.Emit.X64.Frame) (pc : Int64) (d : Scc.IR.Reg)
    (h : Nat) (kv : UInt64) (u : Scc.IR.Operand) (J J1 : AS → Ctl → Prop) : Prop :=
  ∀ (lw : List Item) (off : Int) (zs : List Nat) (zc z k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → rsOf fr d = some off →
    zs.length = (dirs lw).length →
    let L := (_root_.Executable.labels exe).label
    let pcB := pc + Int64.ofNat zs.sum
    let pcR := pcB + Int64.ofNat zc
    let B := [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]
    let Jc := nbJc L B pcB (oB fr) J1
    Cd pc ((dirs lw).zip zs) → Bl pcB zc Scc.Lower.Names.alloc k → Cd pcR [(stDir off, z)] →
    BlkW (W₀ lbl lsize) K exe endPc R F ⟨pc, oB fr, J⟩ ((dirs lw).zip zs) ∧
    BlkW (W₀ lbl lsize) K exe endPc R F ⟨pcB, oB fr, J1⟩ B ∧
    (∀ σ c, J1 σ c → ∃ q : Call, q.OK ms L ∧ q.c0 = c ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms) ∧
    (∀ q : Call, q.OK ms L → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) ∧
    (∀ q : {q : Call // q.OK ms L}, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx ms L R fr.size Jc q.1 m) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F' (Ea ms q.1 l b w) s c →
        TP tp s → ms.xa l b w s c) ∧
    (∀ q : Call, q.OK ms L → q.ra = pcR.toBitVec →
      AllocW ms q (fun s c => TP tp s → W₀ lbl lsize s c) K exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8)
        (fun m => F m ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m ∧ AllocCtx ms L R fr.size Jc q m)) ∧
    (∀ q : Call, q.OK ms L → ∀ l b old, lbl l = some b → b = ms.heap + 16 * old + ms.off q.n q.τ →
      old + ms.units q.n q.τ ≤ ms.cells → q.n ≤ lsize l) ∧
    ∀ (lbl' : WeakMem.AllocLabel → Option Nat) (lsize' : WeakMem.AllocLabel → Nat),
      (∀ l b, lbl l = some b → lbl' l = some b) → (∀ l, lsize l ≤ lsize' l) →
      BlkW (W₀ lbl' lsize') K exe endPc R F ⟨pcR, oB fr, nbJS ms L lbl' lsize' R fr.size tp Jc⟩ [(stDir off, z)]

/-- **`AllocW2` at every allocation of a body** (`newBufC_of`'s premise):
at each `let x = newBuf cn τ in e` at `pc` (label counter `kk`) with the
ghost `c0` in `G0`, the term in `T`, `env` fresh at `n`, the count `cn` the
immediate `kv`, the element counts `en`, `em` and the header `h`
(`lowerC2_newBuf_inv`'s data) and the allocation's resumption facts
(`PtC2`), `AllocW2` at the call's arguments `h`, `kv`, `unitsOf …` into
`x%n`. -/
def AllocW2At (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isa)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : MemSide isa) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) :
    Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : CoreTerm.At) (τ : Ty) (e : Expr) (env : Scc.Lower.Env)
    (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (tk : Ty) (kv : UInt64)
    (en em h : Nat), G0 c0 → T (.let_ x (.newBuf cn τ) e) → Fresh env n →
    atomV env cn = some (tk, [.imm kv]) → Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) →
    Scc.Obj.header0 lcx.obj .array en em = some h →
    PtC2 lcx fr Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e) →
    AllocW2 Cd Bl W₀ K exe endPc R F ms lbl lsize tp fr pc (regName x n) h kv
      (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)
      (laneJ p lbl lsize i fr fp ra tp c0 pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
        (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))

/-! ## The construct -/

section Main

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {W : FragS isa} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node at the frame's offsets has `%rbp` at the frame record.** -/
theorem at_oB_rbp {fr : Scc.Emit.X64.Frame} {pc : Int64} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, oB fr, J⟩ s c) :
    At exe endPc R F ⟨pc, oB fr, fun σ c => J σ c ∧ σ.regs.get64 .rbp = R.addr 0⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hj⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, hj, hA.so .rbp 0 (by simp [oB, SO.get, lk])⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The arguments' loads** into `%rdi`, `%rsi`, `%rdx` from the node at
the allocation (`bodyN2` with the `%fs` base) to the `callq` (`nbJ1`): the
source's local run taken to the allocation exactly. -/
theorem nbArgs_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat} {c0 : Ctl} {pc : Int64} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {lw : List Item} (hlw : getOps fr ([a0, a1, a2].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) (hc : CdOf exe endPc pc ((dirs lw).zip zs))
    (hWB : BlkW W₀ K exe endPc R F ⟨pc, oB fr, laneJ p lbl lsize i fr fp ra tp c0 pc t env lits cs bufs⟩
      ((dirs lw).zip zs)) :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0 pc t (ofEnv2 env) lits cs bufs).withTp tp))
      (At exe endPc R F ⟨pc + Int64.ofNat zs.sum, oB fr,
        nbJ1 p lbl lsize fr R fp ra tp c0 t env lits cs bufs a0 a1 a2⟩) := by
  refine (seg_blk1 (lo := -(fr.size : Int)) (hi := 16)
    (n := ⟨pc, oB fr, fun σ c => laneJ p lbl lsize i fr fp ra tp c0 pc t env lits cs bufs σ c ∧
      σ.regs.get64 .rbp = R.addr 0⟩) hF hR hlo hhi hc (BlkW.mono hWB rfl rfl fun _ _ h => h.1)
    (args3_ne_nil hlw hz) (okBlk_args3 hf h1 hlw hz) ?_).mono_pre fun s c h => at_oB_rbp h
  rintro σ c ⟨⟨⟨⟨L, sm, B, c', hr, hj, hn, hb, hm, hS⟩, hfj, hc0, -⟩, htp⟩, hrbp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨va, vb, vc, hva, hvb, hvc, rg, h0, h1', h2, htp', hrbp', hrun⟩ :=
    args3_step hf h1 hlw hz (_root_.Executable.labels exe).label pc σ
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  rw [hrun]
  exact ⟨rfl, so_le_oB fr, by rw [h0]; exact hva, by rw [h1']; exact hvb, by rw [h2]; exact hvc, hfj,
    by rw [htp']; exact htp, by rw [hrbp']; exact hrbp, hc0.trans hr, L, sm, B, hj, hn, hb, hm, hS⟩

/-- A call's premises under `tpXa` (`callOK_tp`). -/
theorem callOK_tpXa {ms0 : MemSide isa} {t : UInt64} {lab : Label → Int64} {q : Call} (h : q.OK ms0 lab) :
    q.OK (tpXa ms0 t) lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

/-- A call's premises from `tpXa` (`callOK_untp`). -/
theorem callOK_untpXa {ms0 : MemSide isa} {t : UInt64} {lab : Label → Int64} {q : Call}
    (h : q.OK (tpXa ms0 t) lab) : q.OK ms0 lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- The allocator's states under `tpXa` (`allocW_tp`). -/
theorem allocW_tpXa {ms0 : MemSide isa} {t : UInt64} {q : Call} {W₀ : Frag isa} {R' : Region}
    {F' : MachineData → Prop} (h : AllocW ms0 q W₀ K exe endPc R' F') :
    AllocW (tpXa ms0 t) q W₀ K exe endPc R' F' :=
  ⟨h.e, h.entry, h.j1, h.cnt, h.c1, h.rmw, h.c2, h.j2, h.slow, h.j3, h.full, h.ok, h.f1, h.o1, h.f2, h.o2, h.s2,
    h.o3, h.f3, h.o4, h.f4, h.o5, h.f5, h.o6, h.f6, h.o7, h.f7, h.o8, h.hdr, h.o9, h.ret⟩

/-- **The allocator's call** from the `callq` at `pcB` (`J1`, the `%fs`
base `tp`) to its return at `pcB + zc` or its heap abort (`nbX`), the `%fs`
base kept (`newBuf_blkW` under `tpXa`, inside `NoSetFsW`, `SegW.keepTPN'`):
`AllocW2`'s premises at the call, the allocator's states asked inside `W₀`
only at `fsBase = tp` (`hW`; `keepTPN'` carries `TP tp` from `J1`'s `hJtp`
along the call). -/
theorem nbCall_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hprog : Alloc.allocIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} (hK : ms0.K = some Scc.Sem.X64.abi) {W₀ : Frag isa} {tp : UInt64} {pcB : Int64}
    {zc : Nat} {J1 : AS → Ctl → Prop} (hJtp : ∀ σ c, J1 σ c → σ.regs.fsBase = tp)
    (hc : CdOf exe endPc pcB [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)])
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB, oB fr, J1⟩ [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)])
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms0 (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms0)
    (hmem : ∀ q : Call, q.OK ms0 (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms0.ctr ∨ ∃ o, o + ms0.units q.n q.τ ≤ ms0.cells ∧ a.toNat = q.hdrAt ms0 o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms0 (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx ms0 (_root_.Executable.labels exe).label R fr.size
        (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr) J1)
        q.1 m) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F' (Ea ms0 q.1 l b w) s c →
        TP tp s → ms0.xa l b w s c)
    (hW : ∀ q : Call, q.OK ms0 (_root_.Executable.labels exe).label → q.ra = (pcB + Int64.ofNat zc).toBitVec →
      AllocW ms0 q (fun s c => TP tp s → W₀ s c) K exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8)
        (fun m => F m ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m ∧
          AllocCtx ms0 (_root_.Executable.labels exe).label R fr.size
            (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB
              (oB fr) J1) q m)) :
    SegW W₀ K p lbl ms0 (At exe endPc R F ⟨pcB, oB fr, J1⟩)
      (fun s c => (∃ x, At exe endPc R F (nbX ms0 (_root_.Executable.labels exe).label lbl R fr.size
        (pcB + Int64.ofNat zc)
        (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr) J1)
          x) s c) ∧ TP tp s) := by
  have h8 := frame_mod8B hf
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by
    simp only [allocAbortDepth, allocFrame] at hlo; omega
  have h := SegW.keepTPN' (W := W₀) (K := K) (p := p) (lbl := lbl) (t := tp) hK
    (newBuf_blkW (ms := tpXa ms0 tp) (W := NoSetFsW (fun s c => TP tp s → W₀ s c) K) (p := p) (lbl := lbl) hp hend
      hprog hF hR
      (fs := fr.size) (by omega) hlo (by omega) (B := [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]) (pc := pcB)
      (pcR := pcB + Int64.ofNat zc) (o := oB fr) (lo := -(fr.size : Int) - 8) (hi := 16) (J := J1) (J1 := J1)
      (by simp) (okBlk_callq _ _ (by simp [offOk, oB]; omega)) hlo' hhi hc
      (fun σ => by rw [arun_callq]; exact ⟨rfl, by simp [SO.le, oB]⟩) (fun σ c h => ⟨c, .refl c, h⟩)
      (fun σ c h => by
        obtain ⟨q, hok, hc0, h0, h1, h2⟩ := hq σ c h
        refine ⟨q, callOK_tpXa hok, hc0, ?_, ?_, ?_⟩ <;> rw [arun_callq] <;> simpa [Reg64s.set64])
      (fun σ c _ => by rw [arun_callq]; simp [upd_apply, oB]) (fun q hok => hmem q (callOK_untpXa hok))
      (fun q F' hF' hctx l b w s c hl hAt hT => hxa ⟨q.1, callOK_untpXa q.2⟩ F' hF' hctx l b w s c hl hAt hT)
      (BlkW.noSetFs (fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
        ⟨fun _ => (hWB s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
          (hWB s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩) hc rfl)
      (fun q hok hra => allocW_tpXa (AllocW.noSetFs hp hend hprog (hW q (callOK_untpXa hok) hra))))
    fun _ _ hw ht => hw ht
  refine (h.mono_pre fun s c hA => ⟨hA, ?_⟩).mono_post fun s c ⟨⟨x, hx⟩, ht⟩ => ⟨?_, ht⟩
  rotate_left
  · cases x with
    | ret =>
      obtain ⟨he, hn, hd, hpc, σ, hA, hFm, q, hC, hE⟩ := hx
      exact ⟨.ret, he, hn, hd, hpc, σ, hA, hFm, ⟨q.1, callOK_untpXa q.2⟩, hC, hE⟩
    | abort =>
      obtain ⟨he, hn, hd, hpc, σ, hA, hFm, h2, q, hJ, hC⟩ := hx
      exact ⟨.abort, he, hn, hd, hpc, σ, hA, hFm, h2, ⟨q.1, callOK_untpXa q.2⟩, hJ, hC⟩
  obtain ⟨-, -, -, -, σ, hAb, -, hJ⟩ := hA
  show s.st.1.regs.fsBase = tp
  rw [hAb.regs]; exact hJtp σ c hJ

omit [Kraken.Executable.ValidLayout exe] in
/-- **The returned base's store into `x%n`** from the landing (`nbJS` at
`lbl'`, `lsize'`, on either route) to the node at `e` with `x` bound
(`bodyN2` at `lbl'`, `lsize'`, the ghost run past the allocation): the
allocator keeps the frame's cells; the caller's facts at `lbl`, `lsize`
carried to `lbl'`, `lsize'` extending them (`hlbl`, `hz`,
`NodeJE.mono_lbl`, `EnvB.mono`); the source past its allocation by
`NJB.newBuf2`; the segment's memory side `ms1` free. -/
theorem nbStore_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 ms1 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64} {i : Expr → String → Nat → Option Nat}
    {c0 : Ctl} {fs : List TermRun.Frame} (pp : Prog) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {lbl' : WeakMem.AllocLabel → Option Nat} {lsize' : WeakMem.AllocLabel → Nat}
    (hlbl : ∀ l b, lbl l = some b → lbl' l = some b) (hzs : ∀ l, lsize l ≤ lsize' l)
    {pcB : Int64} {zc z : Nat} {off : Int} (hoff : rsOf fr (regName x n) = some off)
    (hc : CdOf exe endPc (pcB + Int64.ofNat zc) [(stDir off, z)])
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB + Int64.ofNat zc, oB fr, nbJS ms0 (_root_.Executable.labels exe).label lbl'
      lsize' R fr.size tp (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]
        pcB (oB fr) (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩
      [(stDir off, z)])
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e) :
    SegW W₀ K p lbl' ms1
      (At exe endPc R F ⟨pcB + Int64.ofNat zc, oB fr, nbJS ms0 (_root_.Executable.labels exe).label lbl' lsize' R
        fr.size tp (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB
          (oB fr) (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩)
      (fun s c => ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
        At exe endPc R F ((bodyN2 p lbl' lsize' i fr fp ra c0' (pcB + Int64.ofNat zc + Int64.ofNat z) e
          (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env))
          ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
          (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))).withTp tp) s c) := by
  have hlo0 : R.lo ≤ -(fr.size : Int) - 8 - 160 := by
    simp only [allocAbortDepth, allocFrame] at hlo; omega
  have hlo1 : R.lo ≤ -(fr.size : Int) := by omega
  rw [ofEnv2_cons (group_newBufTy τ _)] at hIt hIc hlb ⊢
  -- the frame's cells are kept by the allocator
  have hout : ∀ k : Int, k % 8 = 0 → -(fr.size : Int) ≤ k → k + 8 ≤ 16 →
      R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-160) 8).Off (k - (-(fr.size : Int) - 8)) :=
    fun k hk8 hk1 hk2 => frame_out hlo0 hhi (by decide) hk8 hk1 hk2
  refine (seg_blk1 (lo := -(fr.size : Int)) (hi := 16)
      (n' := ⟨pcB + Int64.ofNat zc + Int64.ofNat z, oB fr, fun σ c =>
        ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
          ((bodyN2 p lbl' lsize' i fr fp ra c0' (pcB + Int64.ofNat zc + Int64.ofNat z) e
            ((x, newBufTy τ, [.loc (.reg (regName x n)) (Scc.Lower.imm 0)]) :: ofEnv2 env)
            ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
            (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))).withTp tp).J σ c⟩)
      hF hR hlo1 hhi hc hWB
      (by simp) (okBlk_stDir hf h1 hoff z) ?_).mono_post ?_
  · rintro σ c ⟨⟨⟨c1, qx, qa, qτ, qe, qta, qws, qn, qh, qfp, qra⟩, hq⟩, ⟨σC, ⟨σ0, hJ1, hσC⟩, hsl⟩,
      l, ini, old, rfl, -, -, hvr, hkz, htp⟩
    obtain ⟨-, -, -, hfj, -, -, hr0, L, sm, B, hj, hn, hb, hm, hS⟩ := hJ1
    have ht := hq.term
    rw [hj.1] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := ht
    have hsl' : ∀ k : Int, k % 8 = 0 → -(fr.size : Int) ≤ k → k + 8 ≤ 16 → σ.slot k = σ0.slot k := by
      intro k hk8 hk1 hk2
      obtain ⟨ho1, ho2⟩ := hout k hk8 hk1 hk2
      rw [hsl k ho1 ho2, hσC, arun_callq]
      simp only [upd_apply, oB]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have hj' : NodeJE lbl' (rsOf fr) (.let_ x (.newBuf cn τ) e) (ofEnv2 env) σ.slot c1 :=
      NodeJE.mono_lbl hlbl ⟨hj.1, hj.2.1, hj.2.2.congr fun _ _ _ _ o' _ => Spike.Lib.Form.opdVal_upd
        fun r k' _ hk' => by
          obtain ⟨hk8, hk1, hk2⟩ := rsOf_bounds hf hk'
          exact hsl' k' (by omega) (by omega) (by omega)⟩
    have hb' := EnvB.mono hb (fun _ h => h) (fun _ h => h) (fun l _ => hzs l)
    have hfr' : ∀ b ∈ ofEnv2 env, ∀ pl ∈ b.2.2, ∀ o' ∈ pl.opds, ∀ r k', o' = .reg r → rsOf fr r = some k' →
        k' ≠ off := fun b hb pl hpl o' ho' r k' hor hrk hk =>
      fresh_ofEnv2 hfr x b hb pl hpl o' ho' r hor (rsOf_inj hf hrk (hk ▸ hoff))
    have hvr' : ValRep lbl' (.loc ⟨l, 0⟩ 0) (σ.regs.get64 .rax).toNat := hvr
    obtain ⟨hd8, -, hd2⟩ := rsOf_bounds hf hoff
    refine ⟨_, .refl _, ?_⟩
    show Hit _ (arun _ _ ⟨pcB + Int64.ofNat zc, oB fr, σ⟩) _
    rw [arun_stDir hf h1 hoff]
    refine ⟨rfl, so_le_oB fr, _, (FrameRunM.ofLocal hr0 fs).trans (FrameRunM.mem1 hj.2.1 hj.1 trivial),
      ⟨⟨_, _, _, NJB.newBuf2 pp hj' hn hb' hm hS he2 hq.ev hq.num l ini hkz hoff hfr' hvr'⟩, ?_, .refl _,
        SlotRepAt.of_nodeJE (NodeJE.newBuf2 hj' he2 qn l ini hoff hfr' hvr') hIt hlb hIc⟩, htp⟩
    refine frJ_upd hf ⟨?_, ?_⟩ hoff _
    · rw [hsl' 0 (by decide) (by omega) (by decide)]; exact hfj.1
    · rw [hsl' 8 (by decide) (by omega) (by decide)]; exact hfj.2
  · rintro s c ⟨he, hn, hd, hpc, σ, hA, hFm, c0', hR', hJ⟩
    exact ⟨c0', hR', he, hn, hd, hpc, σ, hA, hFm, hJ⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The returned base's store on the `.ret` route** (`nbStore_seg` at
`lbl`, `lsize`): the allocator's return (`nbX … .ret`, the `%fs` base `tp`),
`%rbp` as at the call, the label it returns holding the count (`hsz`). -/
theorem nbRet_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64} {i : Expr → String → Nat → Option Nat}
    {c0 : Ctl} {fs : List TermRun.Frame} (pp : Prog) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {pcB : Int64} {zc z : Nat} {off : Int} (hoff : rsOf fr (regName x n) = some off)
    (hc : CdOf exe endPc (pcB + Int64.ofNat zc) [(stDir off, z)])
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB + Int64.ofNat zc, oB fr, nbJS ms0 (_root_.Executable.labels exe).label lbl
      lsize R fr.size tp (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]
        pcB (oB fr) (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩
      [(stDir off, z)])
    (hsz : ∀ q : Call, q.OK ms0 (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      b = ms0.heap + 16 * old + ms0.off q.n q.τ → old + ms0.units q.n q.τ ≤ ms0.cells → q.n ≤ lsize l)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e) :
    SegW W₀ K p lbl ms0
      (fun s c => At exe endPc R F (nbX ms0 (_root_.Executable.labels exe).label lbl R fr.size
        (pcB + Int64.ofNat zc) (nbJc (_root_.Executable.labels exe).label
          [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr)
          (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2)) .ret) s c ∧
        TP tp s)
      (fun s c => ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
        At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0' (pcB + Int64.ofNat zc + Int64.ofNat z) e
          (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env))
          ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
          (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))).withTp tp) s c) := by
  refine (nbStore_seg (ms1 := ms0) (lbl' := lbl) (lsize' := lsize) (fs := fs) hf h1 hF hR hlo hhi pp he2 hfr
    (fun _ _ h => h) (fun _ => Nat.le_refl _) hoff hc hWB hIt hIc hlb).mono_pre ?_
  rintro s c ⟨⟨he, hn, hd, hpc, σ, hA, hFm, q, ⟨σC, hJc, hrbp, hC⟩, l, ini, old, hvr, hc, hx0, hold, -⟩, ht⟩
  have hrb : σ.regs.get64 .rbp = R.addr 0 := by
    obtain ⟨σ0, hJ1, hσC⟩ := hJc
    have h0 : σC.regs.get64 .rbp = σ0.regs.get64 .rbp := by
      rw [hσC, arun_callq]; simp [Reg64s.get64_set64]
    rw [← hJ1.2.2.2.2.2.1, ← h0]
    simp only [Reg64s.get64, hrbp]
  have hA0 : At exe endPc R F ⟨pcB + Int64.ofNat zc, ⟨-(fr.size : Int), []⟩, fun σ' c' => σ' = σ ∧ c' = c⟩ s c :=
    ⟨he, hn, hd, hpc, σ, hA, hFm, rfl, rfl⟩
  have hA' := at_rbp_addr hA0 fun σ' c' h => by rw [h.1]; exact hrb
  obtain ⟨-, -, -, -, σ', hA'', -, hσ', -⟩ := hA'
  subst hσ'
  refine ⟨he, hn, hd, hpc, σ', hA'', hFm, q, ⟨σC, hJc, hC⟩, l, ini, old, hc, hx0, hold, hvr, ?_, hA.regs ▸ ht⟩
  obtain ⟨-, v, hv, hrv⟩ := hvr
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hv
  obtain ⟨b, hb', rfl⟩ := hv
  exact hsz _ q.2 l b old hb' (by omega) hold

/-- **The free variables at an allocation are bound** (`htot` at its
`let`): the count atom's variable by `atomV`, the continuation's others
than `x` by its own (`hIt`). -/
theorem htot_newBuf {env : Scc.Lower.Env} {x : String} {cn : At} {τ : Ty} {e : Expr} {n : Nat} {tk : Ty}
    {kv : UInt64} (hat : atomV env cn = some (tk, [.imm kv]))
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome) :
    ∀ y ∈ Scc.Sem.exprFv (.let_ x (.newBuf cn τ) e), (lookupS (ofEnv2 env) y).isSome := by
  intro y hy
  simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.mem_append, List.mem_filter,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
  rcases hy with hy | ⟨hy, hne⟩
  · cases cn with
    | var z =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      simp only [atomV, Option.map_eq_some_iff] at hat
      obtain ⟨b, hb, -⟩ := hat
      rw [lookupS_ofEnv2, hb]; rfl
    | lit _ => simp [Scc.Sem.atVars] at hy
    | unit => simp [Scc.Sem.atVars] at hy
  · have h := hIt y hy
    rw [lookupS_ofEnv2] at h ⊢
    have hne' : x ≠ y := fun h => by subst h; simp at hne
    simpa [List.find?_cons, hne'] using h

/-- **The call node of an allocation**: each of its controls placed in the
slot file (`SlotRepAt` at the frame's register slots), at a `newBuf` of an
`elem2` element type. -/
def NbJcOf (i : Expr → String → Nat → Option Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (fr : Scc.Emit.X64.Frame) (Jc : AS → Ctl → Prop) : Prop :=
  ∀ σ c, Jc σ c → SlotRepAt i lbl (rsOf fr) σ.slot c ∧
    ∃ x cn τ e, c.term = .let_ x (.newBuf cn τ) e ∧ Scc.Lower.elem2 τ = true

/-- **The allocation's call node is `NbJcOf`** (`nbJc` of `nbJ1`): the
`callq`'s push is below the frame (`arun_callq`, `opdVal_upd_out`), the
source at the `let` placed by its `NodeJE` and the walk's facts there
(`SlotRepAt.of_nodeJE`). -/
theorem nbJcOf_nbJ1 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {R : Region} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String}
    {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand} {i : Expr → String → Nat → Option Nat}
    (lab : Label → Int64) (pc : Int64) (zc : Nat)
    (he2 : Scc.Lower.elem2 τ = true)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.newBuf cn τ) e), (lookupS (ofEnv2 env) y).isSome)
    (hlb : LocBaseRegAt (ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    (himm : ImmIn i (ofEnv2 env) (.let_ x (.newBuf cn τ) e)) :
    NbJcOf i lbl fr (nbJc lab [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pc (oB fr)
      (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2)) := by
  rintro σ c ⟨σ0, ⟨-, -, -, -, -, -, -, L, sm, B, hj, -⟩, rfl⟩
  rw [arun_callq]
  obtain ⟨ht, hh, hs⟩ := hj
  have hj' : NodeJE lbl (rsOf fr) (.let_ x (.newBuf cn τ) e) (ofEnv2 env)
      (upd σ0.slot ((oB fr).sp - 8) (pc + Int64.ofNat zc).toBitVec) c :=
    ⟨ht, hh, hs.congr fun _ _ _ _ o _ =>
      opdVal_upd_out hf (by simp only [oB]; omega) σ0.slot _ o⟩
  exact ⟨SlotRepAt.of_nodeJE hj' htot hlb himm, x, cn, τ, e, ht, he2⟩

/-- **The allocation's call node is at the allocation's term** (`nbJc` of
`nbJ1`, its `NodeJE`'s term): so at the walk predicate `T` there
(`newBufC_of`'s `hAb` premise). -/
theorem nbJc_nbJ1_term {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {fr : Scc.Emit.X64.Frame} {R : Region} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr}
    {env : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {a0 a1 a2 : Scc.IR.Operand} (lab : Label → Int64) (blk : List (Directive × Nat)) (pc : Int64) :
    ∀ σ c, nbJc lab blk pc (oB fr) (nbJ1 p lbl lsize fr R fp ra tp c0 t env lits cs bufs a0 a1 a2) σ c →
      c.term = t := by
  rintro σ c ⟨σ0, ⟨-, -, -, -, -, -, -, L, sm, B, ⟨ht, -⟩, -⟩, -⟩
  exact ht

/-- **A buffer allocation of an `Accepted2` body** (`NewBufC`) in a valid
layout of cells with the allocator's code (`allocIn`), the frame's region
reaching the allocator's heap abort (`hlo`): the code predicates give code
(`hCd`, `hBl`); the memory side's `K` is the ABI's (`hK`, the `%fs` base
kept across the allocator); the element types are `elem2` (`hTn`); the
source's controls in `G0` closed under the frame runs with memory; the
memory side's states and the allocator's premises at each allocation's own
arguments (`AllocW2At`); the allocator's heap abort, from a call node
`NbJcOf`, is one of `Ab` (`hAb`). -/
theorem newBufC_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Alloc.allocIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int)) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isa}
    (hW₀ : ∀ s c, W₀ lbl lsize s c → W s c fs) (hK : (ms fs).K = some Scc.Sem.X64.abi)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {Ab : FragS isa} (lcx : Scc.Lower.Ctx)
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hAW : AllocW2At p lbl lsize lcx fr Cd Bl W₀ K exe endPc R F (ms fs) fp ra tp G0 i T Lk)
    (hAb : ∀ (Jc : AS → Ctl → Prop) (pcR : Int64) s c, NbJcOf i lbl fr Jc → (∀ σ c', Jc σ c' → T c'.term) →
      At exe endPc R F (nbX (ms fs) (_root_.Executable.labels exe).label lbl R fr.size pcR Jc .abort) s c →
        Ab s c fs) :
    NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk kk' env n x cn τ e tk kv en em h lits cs bufs hc0 hT hfr _ _ _ _ hat hco hhd _ hi hIt hIc hlb hpt
  have he2 := hTn x cn τ e hT
  obtain ⟨himmL, -, -, -, hlbL⟩ : ImmIn i (ofEnv2 env) (.let_ x (.newBuf cn τ) e) ∧ T (.let_ x (.newBuf cn τ) e) ∧
      EnvTy2 (.let_ x (.newBuf cn τ) e, env, n) ∧ GrpL env ∧ LocBaseRegAt (ofEnv2 env) (.let_ x (.newBuf cn τ) e) := by
    obtain ⟨-, -, -, -, -, -, hw, -⟩ := hpt
    exact walk2_head hw
  have hlo1 : R.lo ≤ -(fr.size : Int) := by
    simp only [allocAbortDepth, allocFrame] at hlo; omega
  obtain ⟨lw, off, zs, zc, z, hlw, hoff, hz, hcla, hbl, hcls, -, rfl⟩ := instsC2_newBuf hi
  obtain ⟨hWla, hWbl, hq, hmem, hxa, hW, hsz, hWls⟩ :=
    hAW c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpt lw off zs zc z kk hlw hoff hz
      hcla hbl hcls
  -- the arguments' loads
  have s1 := nbArgs_seg (p := p) (lbl := lbl) (lsize := lsize) (K := K) (ms0 := ms fs) (i := i) hf h1 hF hR
    hlo1 hhi hlw hz (hCd _ _ hcla) hWla
  -- the allocator's call, the `%fs` base kept
  have s2 := nbCall_seg (p := p) (lbl := lbl) hf hp hend hprog hF hR hlo hhi hK
    (fun σ c hJ => hJ.2.2.2.2.1) (hBl _ _ _ _ hbl) hWbl hq hmem hxa hW
  -- the returned base's store
  have s3 := nbRet_seg (p := p) (lbl := lbl) (lsize := lsize) (i := i) (c0 := c0) (fs := fs) hf h1 hF hR
    hlo hhi lcx.prog he2 hfr hoff (hCd _ _ hcls) (hWls lbl lsize (fun _ _ h => h) (fun _ => Nat.le_refl _)) hsz
    hIt hIc hlb
  have s12 := (s1.seq s2).mono_post (Q' := fun s c =>
    (At exe endPc R F (nbX (ms fs) (_root_.Executable.labels exe).label lbl R fr.size
      (pc + Int64.ofNat zs.sum + Int64.ofNat zc)
      (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]
        (pc + Int64.ofNat zs.sum) (oB fr)
        (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
          (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))) .ret) s c ∧ TP tp s) ∨ Ab s c fs)
    fun s c ⟨⟨xx, hx⟩, ht⟩ => by
      cases xx with
      | ret => exact .inl ⟨hx, ht⟩
      | abort =>
        exact .inr (hAb _ _ s c (nbJcOf_nbJ1 hf _ _ _ he2 (htot_newBuf hat hIt) hlbL himmL)
          (fun σ c' hc => (nbJc_nbJ1_term _ _ _ σ c' hc) ▸ hT) hx)
  refine (SegWS.liftS fs (s12.seq_left s3) hW₀).mono_post ?_
  rintro s c fs' ⟨h | h, rfl⟩
  · exact .inl ⟨rfl, h⟩
  · exact .inr h

omit [Kraken.Executable.ValidLayout exe] in
/-- **A buffer allocation's tail on the fresh-label route**: from the
allocator's continuation at the fresh label `l`, base `b` (`Ea`, in the
allocator's region under a frame condition `F'` below `F` in the call's
context `hctx`, the `%fs` base `tp`) to `ContC` at the label map `lbl'`
placing `l` at `b` (`hl'`) and extending `lbl` (`hlbl`), the sizes `lsize'`
extending `lsize` (`hz`) and holding the count at `l` (`hkz`): the
allocator's region left (`at_leave`) at the landing (`nbJS`, the return
address the `callq`'s, `%rbp` back at the frame record), then the returned
base's store (`nbStore_seg`, the store's states in `W₀`: `AllocW2`'s last
premise at `lbl'`, `lsize'`). -/
theorem newBufC_tail {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64} {i : Expr → String → Nat → Option Nat}
    {c0 : Ctl} {fs : List TermRun.Frame} (hW₀ : ∀ s c, W₀ s c → W s c fs) {Ab : FragS isa} (pp : Prog)
    {x : String} {cn : At} {τ : Ty} {e : Expr}
    (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {pcB : Int64} {zc z : Nat} {off : Int} (hoff : rsOf fr (regName x n) = some off)
    (hc : CdOf exe endPc (pcB + Int64.ofNat zc) [(stDir off, z)])
    {lbl' : WeakMem.AllocLabel → Option Nat} {lsize' : WeakMem.AllocLabel → Nat}
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB + Int64.ofNat zc, oB fr, nbJS ms0 (_root_.Executable.labels exe).label lbl'
      lsize' R fr.size tp (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]
        pcB (oB fr) (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩
      [(stDir off, z)])
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    {q : Call} (hq : q.OK ms0 (_root_.Executable.labels exe).label)
    {F' : MachineData → Prop} (hF' : ∀ m, F' m → F m)
    (hctx : ∀ m, F' m → AllocCtx ms0 (_root_.Executable.labels exe).label R fr.size
      (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr)
        (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2)) q m)
    {l : WeakMem.AllocLabel} {b w : Nat} (hlbl : ∀ l b, lbl l = some b → lbl' l = some b)
    (hl' : lbl' l = some b) (hz : ∀ l, lsize l ≤ lsize' l) (hkz : q.n ≤ lsize' l)
    {ms' : List TermRun.Frame → MemSide isa} :
    SegWS W K p lbl' ms'
      (Frag.at (fun s c => At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F' (Ea ms0 q l b w) s c ∧
        TP tp s) fs)
      (ContC p lbl' lsize' i fr exe endPc R F fp ra tp c0 fs Ab (pcB + Int64.ofNat zc + Int64.ofNat z) e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))) := by
  have s3 := nbStore_seg (ms1 := ms' fs) (lbl' := lbl') (lsize' := lsize') (i := i) (c0 := c0) (fs := fs)
    hf h1 hF hR hlo hhi pp he2 hfr hlbl hz hoff hc hWB hIt hIc hlb
  refine ((SegWS.liftS fs s3 hW₀).mono_pre ?_).mono_post ?_
  · rintro s c fs' ⟨⟨hA, ht⟩, hfs⟩
    refine ⟨?_, hfs⟩
    have hL := at_leave (P := fun σC => ∃ c, nbJc (_root_.Executable.labels exe).label
        [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr)
        (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2) σC c ∧
        (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms0 q .e).J
          (enter (-(fr.size : Int) - 8) σC) c) rfl
      (fun m hm => ⟨hF' m hm, by
        obtain ⟨mC, σC, c, hAb, hJ, hN, hK⟩ := hctx m hm
        exact ⟨mC, σC, _, hK, hAb, c, hJ, hN⟩⟩) hA
    obtain ⟨he, hn, hd, hpc, σ, hAs, hFm, σx, σC, ⟨ini, old, hc, hx0, hb, hold, hfpx, -⟩,
      ⟨c', ⟨σ0, hJ1, hσC⟩, hc', hfpC, h30, -⟩, rfl⟩ := hL
    have hra : Int64.ofBitVec q.ra = pcB + Int64.ofNat zc := by
      rw [← h30, hσC, arun_callq]
      simp only [enter, upd_apply, oB]
      rw [ite_eq_left (by omega)]
      exact int64_ofBitVec_toBitVec _
    have hrb : (leave (R.callee (-(fr.size : Int) - 8) (-160) 8) (-(fr.size : Int) - 8) σC σx).regs.get64 .rbp =
        R.addr 0 := by
      have h0 : σC.regs.get64 .rbp = σ0.regs.get64 .rbp := by
        rw [hσC, arun_callq]; simp [Reg64s.get64_set64]
      rw [← hJ1.2.2.2.2.2.1, ← h0]
      show σx.regs.get64 .rbp = σC.regs.get64 .rbp
      simp only [Reg64s.get64]
      exact hfpx.trans hfpC.symm
    have e8 : -(fr.size : Int) - 8 + 8 = -(fr.size : Int) := by omega
    rw [e8] at hAs
    have hA0 : At exe endPc R F ⟨pcB + Int64.ofNat zc, ⟨-(fr.size : Int), []⟩, fun σ' c' =>
        σ' = leave (R.callee (-(fr.size : Int) - 8) (-160) 8) (-(fr.size : Int) - 8) σC σx ∧ c' = c⟩ s c :=
      ⟨he, hn, hd, by rw [← hra]; exact hpc, _, hAs, hFm, rfl, rfl⟩
    have hA' := at_rbp_addr hA0 fun σ' c' h => by rw [h.1]; exact hrb
    obtain ⟨-, -, -, -, σ', hA'', -, hσ', -⟩ := hA'
    subst hσ'
    refine ⟨he, hn, hd, by rw [← hra]; exact hpc, _, hA'', hFm, ⟨q, hq⟩, ⟨σC, hc' ▸ ⟨σ0, hJ1, hσC⟩, ?_⟩,
      l, ini, old, hc, hx0.trans hb, hold, ⟨by decide, b, by simp [Scc.Sem.wordAddr, hl'], hx0.symm ▸ rfl⟩, hkz,
      hAs.regs ▸ ht⟩
    intro k _ hk
    simp only [leave]
    rw [ite_eq_right hk]
  · rintro s c fs' ⟨h, rfl⟩
    exact .inl ⟨rfl, h⟩

end Main

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.instsC2_newBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.instsC2_newBuf

/-- info: 'Spike.Lib.LowerX64.args3_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.args3_step

/-- info: 'Spike.Lib.LowerX64.nbArgs_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nbArgs_seg

/-- info: 'Spike.Lib.LowerX64.nbCall_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nbCall_seg

/-- info: 'Spike.Lib.LowerX64.nbStore_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nbStore_seg

/-- info: 'Spike.Lib.LowerX64.nbRet_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nbRet_seg

/-- info: 'Spike.Lib.LowerX64.nbJcOf_nbJ1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nbJcOf_nbJ1

/-- info: 'Spike.Lib.LowerX64.newBufC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.newBufC_of

/-- info: 'Spike.Lib.LowerX64.newBufC_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.newBufC_tail
