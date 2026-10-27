/-
**A buffer allocation's premise** (AArch64): `NewBufC` (`Body2.lean`) from
`newBuf_blkWS` (`Spike/Lib/A64AllocS.lean`, the allocator's call after the
argument loads), the source's allocation at any label by a ghost memory
(`EnvB.newBufG`, `Spike/Lib/Src/EnvBGhost.lean`) and the store of the
returned base into `x%n`'s slot.

- `nbJ1`: the call's source relation after the argument loads (the
  arguments in `x0`, `x1`, `x2`, the source at the allocation itself);
- `AllocW2`: the memory side's states at one allocation's caller blocks in
  `W₀` (indexed by the placement, the returned base's store at any
  placement extending the call's) and the allocator's premises (`newBuf_callW_ctx`'s `hq`, `hmem`,
  `hxa`, `hW`) at that call's node (`nbJc`), per use (`LaneW`'s style);
- `AllocStore`, `AllocStoreAt`: `AllocW2`'s returned base's store alone,
  `newBufC_tail`'s premise (`AllocW2.store`, `AllocW2At.store`);
- `htot_newBuf`, `NbJcOf`, `nbJcOf_nbJ1`: the free variables at an
  allocation bound; its call node's controls placed in the slot file at a
  `newBuf` of an `elem2` type (`newBufC_of`'s `hAb` premise, so that the
  heap abort's stub may place them); `nbJc_nbJ1_term`: its controls at
  the allocation's term (so at the walk predicate, `hAb`'s other premise).
-/
import Spike.Lib.LowerA64.LaneC2
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.A64AllocS
import Spike.Lib.Src.NJBNewBuf
import Spike.Lib.Src.NodeJEMono
import Spike.Lib.A64Hello1RodataTP

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.Form (opdVal NodeJE lookupS opdVal_upd)
open Spike.Lib.LowerShape (newBufTy unitsOf)
open Scc.Sem (ValRep)
open Scc.Lower.Inv (regName)
open Spike.Lib.A64.Flow.Ret0 (CallerCells setXReg_TPIDR)
open Spike.Lib.A64.Alloc (Call AllocW Ea)
open Spike.Lib.A64.Flow.NewBuf (nbJc nbX AllocCtx allocAbortDepth newBuf_blkW)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Scc.Cert.Rt.A64 (Lays endOf)

/-! ## The code -/

/-- **`InstsC2`'s allocation arm**: the arguments' loads at `pc`, `bl
scc_rt_alloc` after them (`Bl`), the returned base's store; the pc after
it. -/
theorem insts_newBuf {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {k : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {h : Nat} {kv : UInt64} {u : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl k pc [Spike.Lib.LowerShape.newBufCall d h kv u] pc') :
    ∃ la ls, cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la ∧ cx.setReg d .X0 = .ok ls ∧
      Cd pc (directives la) ∧ Bl (pc + Int64.ofNat (4 * (directives la).length)) Scc.Lower.Names.alloc k ∧
      Cd (pc + Int64.ofNat (4 * (directives la).length) + 4) (directives ls) ∧
      pc' = pc + Int64.ofNat (4 * (directives la).length) + 4 + Int64.ofNat (4 * (directives ls).length) := by
  rcases hi with ⟨hc, -⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨d', h', kv', u', la, ls, he, ha, hs, h1, h2, h3, hp⟩ |
      ⟨_, _, _, he, -⟩
  · simp [Spike.Lib.LowerShape.isCall, Spike.Lib.LowerShape.newBufCall] at hc
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · simp only [Spike.Lib.LowerShape.newBufCall, Scc.IR.Inst.call.injEq, List.cons.injEq, and_true,
      true_and] at he
    obtain ⟨rfl, hh, hk, rfl⟩ := he
    cases hk
    rw [hh]
    exact ⟨la, ls, ha, hs, h1, h2, h3, hp⟩
  · simp [Spike.Lib.LowerShape.newBufCall] at he

/-- **Three register arguments**: `a` into `x0`, `b` into `x1`, `w` into
`x2`. -/
theorem getArgs_three (cx : FnCtx) (a b w : Scc.IR.Operand) :
    cx.getArgs [a, b, w] = (do
      let la ← cx.getOp .X0 a
      let lb ← cx.getOp .X1 b
      let lw ← cx.getOp .X2 w
      return la ++ lb ++ lw) := by
  have hr : argRegs = .X0 :: .X1 :: .X2 :: argRegs.drop 3 := rfl
  have hl : argRegs.length = 8 := rfl
  simp only [FnCtx.getArgs, hl]
  rw [hr]
  cases ha : cx.getOp .X0 a <;> cases hb : cx.getOp .X1 b <;> cases hw : cx.getOp .X2 w <;>
    simp [ha, hb, hw, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn]

/-- **The loads of three arguments** into `x0`, `x1`, `x2`: the slots and
flags unchanged. -/
theorem args3_step {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {a b w : Scc.IR.Operand}
    {l : List Item} (h : cx.getArgs [a, b, w] = .ok l) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ va vb vw : BitVec 64, opdVal (rsOf cx) σ.slot a = some va.toNat ∧
      opdVal (rsOf cx) σ.slot b = some vb.toNat ∧ opdVal (rsOf cx) σ.slot w = some vw.toNat ∧
      ∃ rg : Reg64s, rg.X0.toBitVec = va ∧ rg.X1.toBitVec = vb ∧ rg.X2.toBitVec = vw ∧
        rg.TPIDR_EL0 = σ.regs.TPIDR_EL0 ∧
      arun lab (directives l) ⟨pc, oF cx, σ⟩ =
        ⟨pc + Int64.ofNat (4 * (directives l).length), oF cx, ⟨rg, σ.status, σ.slot⟩⟩ := by
  rw [getArgs_three] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lw, hw, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
    { σ with regs := σ.regs.setXReg .X0 va }
  obtain ⟨vw, hvw, hrw⟩ := arun_getOp hf h1 hw lab
    (pc + Int64.ofNat (4 * (directives la).length) + Int64.ofNat (4 * (directives lb).length))
    { σ with regs := (σ.regs.setXReg .X0 va).setXReg .X1 vb }
  refine ⟨va, vb, vw, hva, hvb, hvw, ((σ.regs.setXReg .X0 va).setXReg .X1 vb).setXReg .X2 vw,
    by simp [Reg64s.setXReg], by simp [Reg64s.setXReg], by simp [Reg64s.setXReg],
    by simp [setXReg_TPIDR], ?_⟩
  simp only [directives_append, arun_append, oF]
  rw [hra, hrb, hrw, pc_add4, pc_add4]
  simp only [List.length_append, Nat.add_assoc]

/-- **The loads of three arguments are covered.** -/
theorem okBlk_args3 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {a b w : Scc.IR.Operand} {l : List Item} (h : cx.getArgs [a, b, w] = .ok l) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) (directives l) = true := by
  rw [getArgs_three] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lw, hw, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have := okBlk_getOp hf h1 h16 hw []
  rw [List.append_nil] at this
  show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
  simp only [directives_append, List.append_assoc]
  rw [okBlk_getOp hf h1 h16 ha, okBlk_getOp hf h1 h16 hb, this]; rfl

/-- **The loads of three arguments are not empty.** -/
theorem args3_ne_nil {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {a b w : Scc.IR.Operand}
    {l : List Item} (h : cx.getArgs [a, b, w] = .ok l) : directives l ≠ [] := by
  rw [getArgs_three] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lw, hw, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [directives_append, ne_eq, List.append_eq_nil_iff, not_and]
  exact fun h0 => absurd h0.1 (getOp_ne_nil hf h1 ha)

/-! ## The call's nodes -/

/-- **The call's source relation after the argument loads** (`newBuf_blkW`'s
`J1`): the operands `a0`, `a1`, `a2` valued in `x0`, `x1`, `x2`, the saved
pair, the thread pointer `tp`, the source at the allocation itself (`c1`,
reached from the ghost `c0`) with the node's invariant up to the buffers'
literal lengths at `t` and the environment's literal, buffer and size
facts. -/
def nbJ1 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cx : FnCtx)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (a0 a1 a2 : Scc.IR.Operand) :
    AS → Ctl → Prop :=
  fun σ c1 => opdVal (rsOf cx) σ.slot a0 = some σ.regs.X0.toBitVec.toNat ∧
    opdVal (rsOf cx) σ.slot a1 = some σ.regs.X1.toBitVec.toNat ∧
    opdVal (rsOf cx) σ.slot a2 = some σ.regs.X2.toBitVec.toNat ∧
    FrJ fp ra σ.slot ∧ σ.regs.TPIDR_EL0 = tp ∧ LocalRun p c0 c1 ∧
    ∃ L sm B, NodeJE lbl (rsOf cx) t (ofEnv2 env) σ.slot c1 ∧ EnvLit lits c1.env ∧
      EnvB lits cs bufs L sm lsize c1.env ∧ MemB L sm B ∧ EnvSmall c1.env

/-! ## The memory side's premise -/

/-- **The states after the allocator's return at the landing**, on either
route (the `.ret` exit, or a fresh label's continuation): some call whose
source control a state of the call node `Jc` had, the caller's cells
outside the allocator's region as there, the source past its allocation at
some label, `x0` the base for the counter's old value. -/
def nbL (ms : MemSide isaLSE2) (L : Label → Int64) (R : Region) (fs : Int) (Jc : AS → Ctl → Prop) :
    AS → Ctl → Prop :=
  fun σ c => ∃ q : {q : Call // q.OK ms L},
    (∃ σC, Jc σC q.1.c0 ∧ ∀ k, R.Off k → ¬ (R.callee (-fs) (-160) 0).Off (k - -fs) → σ.slot k = σC.slot k) ∧
    ∃ (l : WeakMem.AllocLabel) (ini old : Nat), c = allocCtl q.1.c0 q.1.x q.1.τ q.1.e q.1.n l ini ∧
      σ.regs.X0.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧ old + ms.units q.1.n q.1.τ ≤ ms.cells

/-- **The landing's facts for the store** at the label map `lbl'` and sizes
`lsize'`: `nbL`'s, the returned label's locative represented by `x0` at
`lbl'` and holding the count at `lsize'`, the thread pointer `tp`. -/
def nbJS (ms : MemSide isaLSE2) (L : Label → Int64) (lbl' : WeakMem.AllocLabel → Option Nat)
    (lsize' : WeakMem.AllocLabel → Nat) (R : Region) (fs : Int) (tp : UInt64) (Jc : AS → Ctl → Prop) :
    AS → Ctl → Prop :=
  fun σ c => ∃ q : {q : Call // q.OK ms L},
    (∃ σC, Jc σC q.1.c0 ∧ ∀ k, R.Off k → ¬ (R.callee (-fs) (-160) 0).Off (k - -fs) → σ.slot k = σC.slot k) ∧
    ∃ (l : WeakMem.AllocLabel) (ini old : Nat), c = allocCtl q.1.c0 q.1.x q.1.τ q.1.e q.1.n l ini ∧
      σ.regs.X0.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧ old + ms.units q.1.n q.1.τ ≤ ms.cells ∧
      ValRep lbl' (.loc ⟨l, 0⟩ 0) σ.regs.X0.toNat ∧ q.1.n ≤ lsize' l ∧ σ.regs.TPIDR_EL0 = tp

/-- **The memory side's states at one allocation's caller blocks in `W₀`
and the allocator's premises**, for the call's code at `Cd`, `Bl` (the
arguments' loads `la` into `x0`, `x1`, `x2` from `pc`, `bl scc_rt_alloc` at
`pcB` after them, the returned base's store `ls` into `d`'s slot at the
landing `pcR`): the states along `la` from `⟨pc, oF cx, J⟩` and at the
`bl` from `J1` lie in `W₀` at the placement `lbl`, `lsize`; along `ls` from
the landing at any placement `lbl'`, `lsize'` extending it (`nbJS`, the
returned label placed at `x0` and holding the count: `lbl` itself on the
`.ret` route, the fresh label added on the other) in `W₀` at `lbl'`,
`lsize'`; at the call's node (`nbJc` of the `bl` from `J1`):
each state's arguments are some call's with its premises (`hq`), the
counter and every header the call may store are unmapped under `F`
(`hmem`), a fresh label's allocation at the thread pointer `tp` lands in
`ms.xa` (`hxa`), and the allocator's states for every
such call returning to `pcR` are inside `W₀` in the call's context (`hW`);
a label already placed at the allocation's base holds its count (`hsz`,
the sizes `lsize`). -/
def AllocW2 (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : MemSide isaLSE2) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (tp : UInt64) (cx : FnCtx) (pc : Int64) (d : Scc.IR.Reg) (h : Nat) (kv : UInt64) (u : Scc.IR.Operand)
    (J J1 : AS → Ctl → Prop) : Prop :=
  ∀ (la ls : List Item) (k : Nat), cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la → cx.setReg d .X0 = .ok ls →
    let L := (_root_.Executable.labels exe).label
    let pcB := pc + Int64.ofNat (4 * (directives la).length)
    let pcR := pcB + 4
    let Jc := nbJc L [blD Scc.Lower.Names.alloc] pcB (oF cx) J1
    Cd pc (directives la) → Bl pcB Scc.Lower.Names.alloc k → Cd pcR (directives ls) →
    BlkW (W₀ lbl lsize) K exe endPc R F ⟨pc, oF cx, J⟩ (directives la) ∧
    BlkW (W₀ lbl lsize) K exe endPc R F ⟨pcB, oF cx, J1⟩ [blD Scc.Lower.Names.alloc] ∧
    (∀ σ c, J1 σ c → ∃ q : Call, q.OK ms L ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms) ∧
    (∀ q : Call, q.OK ms L → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) ∧
    (∀ q : {q : Call // q.OK ms L}, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx ms L R cx.frame Jc q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0) F' (Ea ms q.1 l b w) s c →
        TP tp s → ms.xa l b w s c) ∧
    (∀ q : Call, q.OK ms L → q.ra = pcR.toBitVec →
      AllocW ms q (fun s c => TP tp s → W₀ lbl lsize s c) K exe endPc (R.callee (-(cx.frame : Int)) (-160) 0)
        (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧ AllocCtx ms L R cx.frame Jc q m)) ∧
    (∀ q : Call, q.OK ms L → ∀ l b old, lbl l = some b → b = ms.heap + 16 * old + ms.off q.n q.τ →
      old + ms.units q.n q.τ ≤ ms.cells → q.n ≤ lsize l) ∧
    ∀ (lbl' : WeakMem.AllocLabel → Option Nat) (lsize' : WeakMem.AllocLabel → Nat),
      (∀ l b, lbl l = some b → lbl' l = some b) → (∀ l, lsize l ≤ lsize' l) →
      BlkW (W₀ lbl' lsize') K exe endPc R F ⟨pcR, oF cx, nbJS ms L lbl' lsize' R cx.frame tp Jc⟩ (directives ls)

/-- **`AllocW2` at every allocation of a body** (`newBufC_of`'s,
`newBufC_tail`'s premise): at each `let x = newBuf cn τ in e` at `pc`
(label counter `kk`) with the ghost `c0` in `G0`, the term in `T`, `env`
fresh at `n`, the count `cn` the immediate `kv`, the element counts
`en`, `em` and the header `h` (`lowerC2_newBuf_inv`'s data) and the
allocation's resumption facts (`PtC2`), `AllocW2` at the call's
arguments `h`, `kv`, `unitsOf …` into `x%n`. -/
def AllocW2At (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) :
    Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : CoreTerm.At) (τ : Ty) (e : Expr) (env : Scc.Lower.Env)
    (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (tk : Ty) (kv : UInt64)
    (en em h : Nat), G0 c0 → T (.let_ x (.newBuf cn τ) e) → Fresh env n →
    Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) → Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) →
    Scc.Obj.header0 lcx.obj .array en em = some h →
    PtC2 lcx cx Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e) →
    AllocW2 Cd Bl W₀ K exe endPc R F ms lbl lsize tp cx pc (regName x n) h kv
      (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)
      (laneJ p lbl lsize i cx fp ra tp c0 pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
        (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))

/-- **The returned base's store alone** (`AllocW2`'s last field): for the
call's code at `Cd`, `Bl` (the arguments' loads `la` from `pc`, the `bl` at
`pcB`, the store `ls` at the landing `pcR`), the states along `ls` from the
landing at any placement `lbl'`, `lsize'` extending `lbl`, `lsize` (`nbJS`)
in `W₀` at `lbl'`, `lsize'`. This is all `newBufC_tail` uses, and unlike
`AllocW2` it asks nothing of labels already placed (`hsz`). -/
def AllocStore (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : MemSide isaLSE2) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (tp : UInt64) (cx : FnCtx) (pc : Int64) (d : Scc.IR.Reg) (h : Nat) (kv : UInt64) (u : Scc.IR.Operand)
    (J1 : AS → Ctl → Prop) : Prop :=
  ∀ (la ls : List Item) (k : Nat), cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la → cx.setReg d .X0 = .ok ls →
    let L := (_root_.Executable.labels exe).label
    let pcB := pc + Int64.ofNat (4 * (directives la).length)
    let pcR := pcB + 4
    let Jc := nbJc L [blD Scc.Lower.Names.alloc] pcB (oF cx) J1
    Cd pc (directives la) → Bl pcB Scc.Lower.Names.alloc k → Cd pcR (directives ls) →
    ∀ (lbl' : WeakMem.AllocLabel → Option Nat) (lsize' : WeakMem.AllocLabel → Nat),
      (∀ l b, lbl l = some b → lbl' l = some b) → (∀ l, lsize l ≤ lsize' l) →
      BlkW (W₀ lbl' lsize') K exe endPc R F ⟨pcR, oF cx, nbJS ms L lbl' lsize' R cx.frame tp Jc⟩ (directives ls)

/-- `AllocW2`'s store field. -/
theorem AllocW2.store {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {tp : UInt64} {cx : FnCtx} {pc : Int64} {d : Scc.IR.Reg} {h : Nat} {kv : UInt64} {u : Scc.IR.Operand}
    {J J1 : AS → Ctl → Prop} (H : AllocW2 Cd Bl W₀ K exe endPc R F ms lbl lsize tp cx pc d h kv u J J1) :
    AllocStore Cd Bl W₀ K exe endPc R F ms lbl lsize tp cx pc d h kv u J1 :=
  fun la ls k hla hls hc hb hc' => (H la ls k hla hls hc hb hc').2.2.2.2.2.2.2

/-- **The returned base's store at every allocation of a body**
(`newBufC_tail`'s premise): `AllocW2At` with `AllocStore` for `AllocW2`. -/
def AllocStoreAt (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) :
    Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : CoreTerm.At) (τ : Ty) (e : Expr) (env : Scc.Lower.Env)
    (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (tk : Ty) (kv : UInt64)
    (en em h : Nat), G0 c0 → T (.let_ x (.newBuf cn τ) e) → Fresh env n →
    Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) → Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) →
    Scc.Obj.header0 lcx.obj .array en em = some h →
    PtC2 lcx cx Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e) →
    AllocStore Cd Bl W₀ K exe endPc R F ms lbl lsize tp cx pc (regName x n) h kv
      (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)
      (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
        (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))

/-- `AllocW2At`'s store fields. -/
theorem AllocW2At.store {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {lcx : Scc.Lower.Ctx} {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (H : AllocW2At p lbl lsize lcx cx Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T Lk) :
    AllocStoreAt p lbl lsize lcx cx Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T Lk :=
  fun c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpt =>
    (H c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpt).store

/-! ## The construct -/

section Main

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {W : FragS isaLSE2} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The arguments' loads** into `x0`, `x1`, `x2` from the node at the
allocation (`bodyN2` with the thread pointer) to the `bl` (`nbJ1`): the
source's local run taken to the allocation exactly. -/
theorem nbArgs_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat} {c0 : Ctl} {pc : Int64} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {la : List Item} (hla : cx.getArgs [a0, a1, a2] = .ok la) (hc : CdOf exe endPc pc (directives la))
    (hWB : BlkW W₀ K exe endPc R F ⟨pc, oF cx, laneJ p lbl lsize i cx fp ra tp c0 pc t env lits cs bufs⟩
      (directives la)) :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0 pc t (ofEnv2 env) lits cs bufs).withTp tp))
      (At exe endPc R F ⟨pc + Int64.ofNat (4 * (directives la).length), oF cx,
        nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2⟩) := by
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi hc hWB (args3_ne_nil hf h1 hla)
    (okBlk_args3 hf h1 h16 hla) ?_
  rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, hn, hb, hm, hS⟩, hfj, hc0, -⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨va, vb, vw, hva, hvb, hvw, rg, h0, h1', h2, htp', hrun⟩ :=
    args3_step hf h1 hla (_root_.Executable.labels exe).label pc σ
  show Hit _ (arun _ _ ⟨pc, oF cx, σ⟩) c'
  rw [hrun]
  exact ⟨rfl, so_le_refl _ rfl, by rw [h0]; exact hva, by rw [h1']; exact hvb, by rw [h2]; exact hvw, hfj,
    by rw [htp']; exact htp, hc0.trans hr, L, sm, B, hj, hn, hb, hm, hS⟩

/-- A call's premises under `tpXa` (`callOK_tp`). -/
theorem callOK_tpXa {ms0 : MemSide isaLSE2} {t : UInt64} {lab : Label → Int64} {q : Call} (h : q.OK ms0 lab) :
    q.OK (tpXa ms0 t) lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

/-- A call's premises from `tpXa` (`callOK_untp`). -/
theorem callOK_untpXa {ms0 : MemSide isaLSE2} {t : UInt64} {lab : Label → Int64} {q : Call}
    (h : q.OK (tpXa ms0 t) lab) : q.OK ms0 lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- The allocator's states under `tpXa` (`allocW_tp`). -/
theorem allocW_tpXa {ms0 : MemSide isaLSE2} {t : UInt64} {q : Call} {W₀ : Frag isaLSE2} {R' : Region}
    {F' : MachineData → Prop} (h : AllocW ms0 q W₀ K exe endPc R' F') : AllocW (tpXa ms0 t) q W₀ K exe endPc R' F' :=
  ⟨h.e, h.entry, h.n2, h.cnt, h.cnt1, h.cnt2, h.rmw, h.n4, h.n5, h.slow, h.n7, h.full, h.ok, h.ok1, h.ok2,
    h.n12, h.hdr, h.n13, h.ret⟩

/-- **The allocator's call** from the `bl` at `pcB` (`J1`, the thread
pointer `tp`) to its return at `pcB + 4` or its heap abort (`nbX`), the
thread pointer kept (`newBuf_blkW` under `tpXa`, inside `NoMsrW`,
`SegW.keepTPN`): `AllocW2`'s premises at the call. -/
theorem nbCall_seg {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth (cx.frame : Int)) (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2}
    (hK : ms0.K = some Scc.Sem.A64.abi) {W₀ : Frag isaLSE2} {tp : UInt64} {pcB : Int64}
    {J1 : AS → Ctl → Prop} (hJtp : ∀ σ c, J1 σ c → σ.regs.TPIDR_EL0 = tp)
    (hc : CdOf exe endPc pcB [blD Scc.Lower.Names.alloc])
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB, oF cx, J1⟩ [blD Scc.Lower.Names.alloc])
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms0 (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms0)
    (hmem : ∀ q : Call, q.OK ms0 (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms0.ctr ∨ ∃ o, o + ms0.units q.n q.τ ≤ ms0.cells ∧ a.toNat = q.hdrAt ms0 o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms0 (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx ms0 (_root_.Executable.labels exe).label R cx.frame
        (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx) J1) q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0) F' (Ea ms0 q.1 l b w) s c →
        TP tp s → ms0.xa l b w s c)
    (hW : ∀ q : Call, q.OK ms0 (_root_.Executable.labels exe).label → q.ra = (pcB + 4).toBitVec →
      AllocW ms0 q (fun s c => TP tp s → W₀ s c) K exe endPc (R.callee (-(cx.frame : Int)) (-160) 0)
        (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
          AllocCtx ms0 (_root_.Executable.labels exe).label R cx.frame
            (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx) J1) q m)) :
    SegW W₀ K p lbl ms0 (At exe endPc R F ⟨pcB, oF cx, J1⟩)
      (fun s c => (∃ x, At exe endPc R F (nbX ms0 (_root_.Executable.labels exe).label lbl R cx.frame (pcB + 4)
        (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx) J1) x) s c) ∧
        TP tp s) := by
  have h16' := frame_ge16 hf
  have hlo' : R.lo ≤ -(cx.frame : Int) := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame] at hlo; omega
  have hrun : ∀ σ, arun (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
      ⟨pcB, ⟨-(cx.frame : Int), []⟩, σ⟩ = ⟨(_root_.Executable.labels exe).label "scc_rt_alloc",
        ⟨-(cx.frame : Int), []⟩, { σ with regs := σ.regs.setXReg .X30 (pcB + 4).toBitVec }⟩ :=
    fun σ => blD_run _ _ _ _ σ
  have h := SegW.keepTPN' (W := W₀) (K := K) (p := p) (lbl := lbl) (t := tp) hK
    (newBuf_blkW (ms := tpXa ms0 tp) (W := NoMsrW (fun s c => TP tp s → W₀ s c) K) (p := p) (lbl := lbl) hp hend
      hprog hF hR hal
      (fs := cx.frame) (by omega) hlo (by omega) (B := [blD Scc.Lower.Names.alloc]) (pc := pcB) (pcR := pcB + 4)
      (lo := -(cx.frame : Int)) (hi := 0) (J := J1) (J1 := J1) (by simp) (okBlk_blD _ _ _ _) hlo' hhi hc
      (fun σ => by rw [hrun]; exact ⟨rfl, rfl⟩) (fun σ c h => ⟨c, .refl c, h⟩)
      (fun σ c h => by
        obtain ⟨q, hok, hc0, h0, h1, h2⟩ := hq σ c h
        refine ⟨q, callOK_tpXa hok, hc0, ?_, ?_, ?_⟩ <;> rw [hrun] <;> simpa [Reg64s.setXReg])
      (fun σ c _ => by rw [hrun]; simp [Reg64s.setXReg]) (fun q hok => hmem q (callOK_untpXa hok))
      (fun q F' hF' hctx l b w s c hl hAt hT => hxa ⟨q.1, callOK_untpXa q.2⟩ F' hF' hctx l b w s c hl hAt hT)
      (BlkW.noMsr (fun s σ c he hn hdc hpc hA hFm hJ k hk m hA' hD =>
        ⟨fun _ => (hWB s σ c he hn hdc hpc hA hFm hJ k hk m hA' hD).1,
          (hWB s σ c he hn hdc hpc hA hFm hJ k hk m hA' hD).2⟩) hc (by decide))
      (fun q hok hra => allocW_tpXa (AllocW.noMsr (hW q (callOK_untpXa hok) hra) (alloc_code_of hp hend hprog))))
    fun _ _ h ht => h ht
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
  show s.st.1.regs.TPIDR_EL0 = tp
  rw [hAb.regs]; exact hJtp σ c hJ

omit [Kraken.Executable.ValidLayout exe] in
/-- **The returned base's store into `x%n`** from the landing (`nbJS` at
`lbl'`, `lsize'`, on either route) to the node at `e` with `x` bound
(`bodyN2` at `lbl'`, `lsize'`, the ghost run past the allocation): the
allocator keeps the frame's cells; the caller's facts at `lbl`, `lsize`
carried to `lbl'`, `lsize'` extending them (`hlbl`, `hz`,
`NodeJE.mono_lbl`, `EnvB.mono`); the source past its allocation by
`NJB.newBuf2`. -/
theorem nbStore_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth (cx.frame : Int)) (hhi : 0 ≤ R.hi) {ms0 ms1 : MemSide isaLSE2}
    {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64} {i : Expr → String → Nat → Option Nat} {c0 : Ctl}
    {fs : List TermRun.Frame} (pp : Prog) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {lbl' : WeakMem.AllocLabel → Option Nat} {lsize' : WeakMem.AllocLabel → Nat}
    (hlbl : ∀ l b, lbl l = some b → lbl' l = some b) (hz : ∀ l, lsize l ≤ lsize' l)
    {pcB : Int64} {ls : List Item} (hs : cx.setReg (regName x n) .X0 = .ok ls)
    (hc : CdOf exe endPc (pcB + 4) (directives ls))
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB + 4, oF cx, nbJS ms0 (_root_.Executable.labels exe).label lbl' lsize' R
      cx.frame tp (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
        (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩ (directives ls))
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e) :
    SegW W₀ K p lbl' ms1
      (At exe endPc R F ⟨pcB + 4, oF cx, nbJS ms0 (_root_.Executable.labels exe).label lbl' lsize' R cx.frame tp
        (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩)
      (fun s c => ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
        At exe endPc R F ((bodyN2 p lbl' lsize' i cx fp ra c0' (pcB + 4 + Int64.ofNat (4 * (directives ls).length)) e
          (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env))
          ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
          (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))).withTp tp) s c) := by
  have h16' := frame_ge16 hf
  have hlo0 : R.lo ≤ -(cx.frame : Int) - 160 := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame] at hlo; omega
  have hlo1 : R.lo ≤ -(cx.frame : Int) := by omega
  have hok := okBlk_resStore hf h1 h16 hs
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf cx (regName x n) = some (o - cx.frame) := by simp [rsOf, ho]
  have hle := ofs_le hf ho
  rw [setReg_eq hf (by omega) ho] at hs
  cases ok_inj hs
  have hds : directives [ins (.STR (rz .W64 .X0) ⟨spW64, .imm ⟨i64 o, none⟩⟩)] =
      [spStr .X0 (Int64.ofInt o)] := rfl
  rw [hds] at hc hok hWB ⊢
  rw [ofEnv2_cons (group_newBufTy τ _)] at hIt hIc hlb ⊢
  -- the frame's cells are kept by the allocator
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf cx r = some k' →
      R.Off k' ∧ ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k' - -(cx.frame : Int)) := by
    intro r k' hk'
    unfold rsOf at hk'
    split at hk'
    · rename_i o' ho'
      cases hk'
      obtain ⟨h0, h8, hle'⟩ := slotOff_bounds hf ho'
      exact frame_outC (by decide) hlo0 hhi (by omega) (by omega) (by omega)
    · cases hk'
  have houtA : R.Off (-16) ∧ ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (-16 - -(cx.frame : Int)) :=
    frame_outC (by decide) hlo0 hhi (by decide) (by omega) (by omega)
  have houtB : R.Off (-8) ∧ ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (-8 - -(cx.frame : Int)) :=
    frame_outC (by decide) hlo0 hhi (by decide) (by omega) (by omega)
  refine (seg_blk1 (lo := -(cx.frame : Int))
      (n' := ⟨pcB + 4 + Int64.ofNat (4 * [spStr .X0 (Int64.ofInt o)].length), oF cx, fun σ c =>
        ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
          ((bodyN2 p lbl' lsize' i cx fp ra c0' (pcB + 4 + Int64.ofNat (4 * [spStr .X0 (Int64.ofInt o)].length)) e
            ((x, newBufTy τ, [.loc (.reg (regName x n)) (Scc.Lower.imm 0)]) :: ofEnv2 env)
            ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
            (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))).withTp tp).J σ c⟩)
      hF hR hal hlo1 hhi hc hWB (by simp) hok ?_).mono_post ?_
  · rintro σ c ⟨⟨⟨c1, qx, qa, qτ, qe, qta, qws, qn, qh, q29, qra⟩, hq⟩, ⟨σC, ⟨σ0, hJ1, hσC⟩, hsl⟩,
      l, ini, old, rfl, -, -, hvr, hkz, htp⟩
    obtain ⟨-, -, -, hfj, -, hr0, L, sm, B, hj, hn, hb, hm, hS⟩ := hJ1
    have ht := hq.term
    rw [hj.1] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := ht
    have hσs : σC.slot = σ0.slot := by rw [hσC]; erw [blD_run]
    have hsl' : ∀ k', R.Off k' → ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k' - -(cx.frame : Int)) →
        σ.slot k' = σ0.slot k' := fun k' h1 h2 => (hsl k' h1 h2).trans (by rw [hσs])
    have hj' : NodeJE lbl' (rsOf cx) (.let_ x (.newBuf cn τ) e) (ofEnv2 env) σ.slot c1 :=
      NodeJE.mono_lbl hlbl ⟨hj.1, hj.2.1, hj.2.2.congr fun _ _ _ _ o' _ => opdVal_upd fun r k' _ hk' =>
        hsl' k' (hout r k' hk').1 (hout r k' hk').2⟩
    have hb' := EnvB.mono hb (fun _ h => h) (fun _ h => h) (fun l _ => hz l)
    have hfr' : ∀ b ∈ ofEnv2 env, ∀ pl ∈ b.2.2, ∀ o' ∈ pl.opds, ∀ r k', o' = .reg r → rsOf cx r = some k' →
        k' ≠ o - cx.frame := fun b hb pl hpl o' ho' r k' hor hrk hk =>
      Fresh.ofEnv2 hfr x b hb pl hpl o' ho' r hor (rsOf_inj hrk (hk ▸ hoff))
    have hvr' : ValRep lbl' (.loc ⟨l, 0⟩ 0) σ.regs.X0.toBitVec.toNat := hvr
    refine ⟨_, .refl _, ?_⟩
    show Hit _ (arun _ _ ⟨pcB + 4, ⟨-(cx.frame : Int), []⟩, σ⟩) _
    rw [arun_spStr1, ofs_eq hf h1 ho]
    refine ⟨rfl, so_le_refl _ rfl, _, (FrameRunM.ofLocal hr0 fs).trans (FrameRunM.mem1 hj.2.1 hj.1 trivial),
      ⟨⟨_, _, _, NJB.newBuf2 pp hj' hn hb' hm hS he2 hq.ev hq.num l ini hkz hoff hfr' hvr'⟩, ?_, .refl _,
        SlotRepAt.of_nodeJE (NodeJE.newBuf2 hj' he2 qn l ini hoff hfr' hvr') hIt hlb hIc⟩, htp⟩
    refine frJ_upd ⟨?_, ?_⟩ hle _
    · rw [hsl' _ houtA.1 houtA.2]; exact hfj.1
    · rw [hsl' _ houtB.1 houtB.2]; exact hfj.2
  · rintro s c ⟨he, hn, hd, hpc, σ, hA, hFm, c0', hR', hJ⟩
    exact ⟨c0', hR', he, hn, hd, hpc, σ, hA, hFm, hJ⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The returned base's store on the `.ret` route** (`nbStore_seg` at
`lbl`, `lsize`): the allocator's return (`nbX … .ret`, the thread pointer
`tp`), the label it returns holding the count (`hsz`). -/
theorem nbRet_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth (cx.frame : Int)) (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2}
    {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64} {i : Expr → String → Nat → Option Nat} {c0 : Ctl}
    {fs : List TermRun.Frame} (pp : Prog) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {pcB : Int64} {ls : List Item} (hs : cx.setReg (regName x n) .X0 = .ok ls)
    (hc : CdOf exe endPc (pcB + 4) (directives ls))
    (hWB : BlkW W₀ K exe endPc R F ⟨pcB + 4, oF cx, nbJS ms0 (_root_.Executable.labels exe).label lbl lsize R
      cx.frame tp (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
        (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩ (directives ls))
    (hsz : ∀ q : Call, q.OK ms0 (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      b = ms0.heap + 16 * old + ms0.off q.n q.τ → old + ms0.units q.n q.τ ≤ ms0.cells → q.n ≤ lsize l)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e) :
    SegW W₀ K p lbl ms0
      (fun s c => At exe endPc R F (nbX ms0 (_root_.Executable.labels exe).label lbl R cx.frame (pcB + 4)
        (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2)) .ret) s c ∧
        TP tp s)
      (fun s c => ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
        At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0' (pcB + 4 + Int64.ofNat (4 * (directives ls).length)) e
          (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env))
          ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
          (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))).withTp tp) s c) := by
  refine (nbStore_seg (lbl' := lbl) (lsize' := lsize) hf h1 h16 hF hR hal hlo hhi pp he2 hfr
    (fun _ _ h => h) (fun _ => Nat.le_refl _) hs hc hWB hIt hIc hlb).mono_pre ?_
  rintro s c ⟨⟨he, hn, hd, hpc, σ, hA, hFm, q, hC, l, ini, old, hvr, hc, hx0, hold, -, -⟩, ht⟩
  refine ⟨he, hn, hd, hpc, σ, hA, hFm, q, hC, l, ini, old, hc, hx0, hold, hvr, ?_, hA.regs ▸ ht⟩
  obtain ⟨-, v, hv, hrv⟩ := hvr
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hv
  obtain ⟨b, hb', rfl⟩ := hv
  exact hsz _ q.2 l b old hb' (by omega) hold

/-- **The free variables at an allocation are bound** (`htot` at its
`let`): the count atom's variable by `atomV`, the continuation's others
than `x` by its own (`hIt`). -/
theorem htot_newBuf {env : Scc.Lower.Env} {x : String} {cn : At} {τ : Ty} {e : Expr} {n : Nat} {tk : Ty}
    {kv : UInt64} (hat : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
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
      simp only [Scc.Lower.Inv.atomV, Option.map_eq_some_iff] at hat
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
def NbJcOf (i : Expr → String → Nat → Option Nat) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx)
    (Jc : AS → Ctl → Prop) : Prop :=
  ∀ σ c, Jc σ c → SlotRepAt i lbl (rsOf cx) σ.slot c ∧
    ∃ x cn τ e, c.term = .let_ x (.newBuf cn τ) e ∧ Scc.Lower.elem2 τ = true

/-- **The allocation's call node is `NbJcOf`** (`nbJc` of `nbJ1`): the
`bl` keeps the slot file (`blD_run`), the source at the `let` placed by
its `NodeJE` and the walk's facts there (`SlotRepAt.of_nodeJE`). -/
theorem nbJcOf_nbJ1 {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String} {cn : At} {τ : Ty} {e : Expr}
    {env : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {a0 a1 a2 : Scc.IR.Operand} {i : Expr → String → Nat → Option Nat} (lab : Label → Int64) (pc : Int64)
    (he2 : Scc.Lower.elem2 τ = true)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.newBuf cn τ) e), (lookupS (ofEnv2 env) y).isSome)
    (hlb : LocBaseRegAt (ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    (himm : ImmIn i (ofEnv2 env) (.let_ x (.newBuf cn τ) e)) :
    NbJcOf i lbl cx (nbJc lab [blD Scc.Lower.Names.alloc] pc (oF cx)
      (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2)) := by
  rintro σ c ⟨σ0, ⟨-, -, -, -, -, -, L, sm, B, hj, -⟩, rfl⟩
  have hsl : (arun lab [blD Scc.Lower.Names.alloc] ⟨pc, oF cx, σ0⟩).σ.slot = σ0.slot := by
    erw [blD_run]
  rw [hsl]
  exact ⟨SlotRepAt.of_nodeJE hj htot hlb himm, x, cn, τ, e, hj.1, he2⟩

/-- **The allocation's call node is at the allocation's term** (`nbJc` of
`nbJ1`, its `NodeJE`'s term): so at the walk predicate `T` there
(`newBufC_of`'s `hAb` premise). -/
theorem nbJc_nbJ1_term {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr}
    {env : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {a0 a1 a2 : Scc.IR.Operand} (lab : Label → Int64) (blk : List Directive) (pc : Int64) :
    ∀ σ c, nbJc lab blk pc (oF cx) (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2) σ c →
      c.term = t := by
  rintro σ c ⟨σ0, ⟨-, -, -, -, -, -, L, sm, B, hj, -⟩, -⟩
  exact hj.1

/-- **A buffer allocation of an `Accepted2` body** (`NewBufC`) in a valid
layout of a program with the allocator's code (`allocIn`), the frame's
region reaching the allocator's heap abort (`hlo`): the code predicates
give code (`hCd`, `hBl`); the memory side's `K` is the ABI's (`hK`, the
thread pointer kept across the allocator); the element types are `elem2`
(`hTn`); the source's controls in `G0` closed under the frame runs with
memory; the memory side's states and the allocator's premises at each use
(`AllocW2` at `laneJ`, `nbJ1`); the allocator's heap abort, from a call
node `NbJcOf`, is one of `Ab` (`hAb`). -/
theorem newBufC_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth (cx.frame : Int)) (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64}
    {fs : List TermRun.Frame} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2}
    (hW₀ : ∀ s c, W₀ lbl lsize s c → W s c fs) (hK : (ms fs).K = some Scc.Sem.A64.abi)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {Ab : FragS isaLSE2} (lcx : Scc.Lower.Ctx)
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hAW : AllocW2At p lbl lsize lcx cx Cd Bl W₀ K exe endPc R F (ms fs) fp ra tp G0 i T Lk)
    (hAb : ∀ (Jc : AS → Ctl → Prop) (pcR : Int64) s c, NbJcOf i lbl cx Jc → (∀ σ c', Jc σ c' → T c'.term) →
      At exe endPc R F (nbX (ms fs) (_root_.Executable.labels exe).label lbl R cx.frame pcR Jc .abort) s c →
        Ab s c fs) :
    NewBufC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk env n x cn τ e tk kv en em h lits cs bufs hc0 hT hfr _ _ _ _ hat hco hhd _ hi hIt hIc hlb hpt
  have he2 := hTn x cn τ e hT
  obtain ⟨himmL, -, -, -, hlbL⟩ : ImmIn i (ofEnv2 env) (.let_ x (.newBuf cn τ) e) ∧ T (.let_ x (.newBuf cn τ) e) ∧
      EnvTy2 (.let_ x (.newBuf cn τ) e, env, n) ∧ GrpL env ∧ LocBaseRegAt (ofEnv2 env) (.let_ x (.newBuf cn τ) e) := by
    obtain ⟨-, -, -, -, -, -, hw, -⟩ := hpt
    exact walk2_head hw
  have hlo1 : R.lo ≤ -(cx.frame : Int) := by
    have := frame_ge16 hf
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame] at hlo; omega
  obtain ⟨la, ls, hla, hls, hcla, hbl, hcls, rfl⟩ := insts_newBuf hi
  obtain ⟨hWla, hWbl, hq, hmem, hxa, hW, hsz, hWls⟩ :=
    hAW c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpt la ls kk hla hls hcla hbl
      hcls
  -- the arguments' loads
  have s1 := nbArgs_seg (p := p) (lbl := lbl) (lsize := lsize) (K := K) (ms0 := ms fs) (i := i) hf h1 h16 hF hR
    hal hlo1 hhi hla (hCd _ _ hcla) hWla
  -- the allocator's call, the thread pointer kept
  have s2 := nbCall_seg (p := p) (lbl := lbl) hf h16 hp hend hprog hF hR hal hlo hhi hK
    (fun σ c hJ => hJ.2.2.2.2.1) (hBl _ _ _ hbl) hWbl hq hmem hxa hW
  -- the returned base's store
  have s3 := nbRet_seg (p := p) (lbl := lbl) (lsize := lsize) (i := i) (c0 := c0) (fs := fs) hf h1 h16 hF hR
    hal hlo hhi lcx.prog he2 hfr hls (hCd _ _ hcls) (hWls lbl lsize (fun _ _ h => h) (fun _ => Nat.le_refl _)) hsz
    hIt hIc hlb
  have s12 := (s1.seq s2).mono_post (Q' := fun s c =>
    (At exe endPc R F (nbX (ms fs) (_root_.Executable.labels exe).label lbl R cx.frame
      (pc + Int64.ofNat (4 * (directives la).length) + 4)
      (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
        (pc + Int64.ofNat (4 * (directives la).length)) (oF cx)
        (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
          (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))) .ret) s c ∧ TP tp s) ∨ Ab s c fs)
    fun s c ⟨⟨xx, hx⟩, ht⟩ => by
      cases xx with
      | ret => exact .inl ⟨hx, ht⟩
      | abort =>
        exact .inr (hAb _ _ s c (nbJcOf_nbJ1 _ _ he2 (htot_newBuf hat hIt) hlbL himmL)
          (fun σ c' hc => (nbJc_nbJ1_term _ _ _ σ c' hc) ▸ hT) hx)
  refine ((SegWS.liftS fs (s12.seq_left s3) hW₀).mono_pre fun s c fs' h => h).mono_post ?_
  rintro s c fs' ⟨h | h, rfl⟩
  · exact .inl ⟨rfl, h⟩
  · exact .inr h

omit [Kraken.Executable.ValidLayout exe] in
/-- **A buffer allocation's tail on the fresh-label route**: from the
allocator's continuation at the fresh label `l`, base `b` (`Ea`, in the
allocator's region under a frame condition `F'` below `F` in the call's
context `hctx`, the thread pointer `tp`) to `ContC` at the label map `lbl'`
placing `l` at `b` (`hl'`) and extending `lbl` (`hlbl`), the sizes `lsize'`
extending `lsize` (`hz`) and holding the count at `l` (`hkz`): the
allocator's region left (`at_leave`) at the landing (`nbJS`, the return
address the `bl`'s), then the returned base's store (`nbStore_seg`, the
store's states in `W₀` at `lbl'`, `lsize'` by `AllocStore`, inside `W` by
`hW₀`). -/
theorem newBufC_tail {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth (cx.frame : Int)) (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64}
    {fs : List TermRun.Frame} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isaLSE2}
    {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {Ab : FragS isaLSE2} (lcx : Scc.Lower.Ctx)
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hAW : AllocStoreAt p lbl lsize lcx cx Cd Bl W₀ K exe endPc R F (ms fs) fp ra tp G0 i T Lk)
    {c0 : Ctl} {pc pc' : Int64} {kk : Nat} {env : Scc.Lower.Env} {n : Nat} {x : String} {cn : At} {τ : Ty}
    {e : Expr} {tk : Ty} {kv : UInt64} {en em h : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)}
    (hc0 : G0 c0) (hT : T (.let_ x (.newBuf cn τ) e)) (hfr : Fresh env n)
    (hat : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hco : Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em))
    (hhd : Scc.Obj.header0 lcx.obj .array en em = some h)
    (hpt : PtC2 lcx cx Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e))
    (hi : InstsC2 cx Cd Bl kk pc [Spike.Lib.LowerShape.newBufCall (regName x n) h kv
      (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)] pc')
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    {la : List Item}
    (hla : cx.getArgs [Scc.Lower.imm h, .imm kv, unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv] = .ok la)
    {q : Call} (hq : q.OK (ms fs) (_root_.Executable.labels exe).label)
    {F' : MachineData → Prop} (hF' : ∀ m, F' m → F m)
    (hctx : ∀ m, F' m → AllocCtx (ms fs) (_root_.Executable.labels exe).label R cx.frame
      (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
        (pc + Int64.ofNat (4 * (directives la).length)) (oF cx)
        (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
          (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))) q m)
    {l : WeakMem.AllocLabel} {b w : Nat} {lbl' : WeakMem.AllocLabel → Option Nat}
    {lsize' : WeakMem.AllocLabel → Nat} (hlbl : ∀ l b, lbl l = some b → lbl' l = some b)
    (hl' : lbl' l = some b) (hz : ∀ l, lsize l ≤ lsize' l) (hkz : q.n ≤ lsize' l)
    (hW₀ : ∀ s c, W₀ lbl' lsize' s c → W s c fs)
    {ms' : List TermRun.Frame → MemSide isaLSE2} :
    SegWS W K p lbl' ms'
      (Frag.at (fun s c => At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0) F' (Ea (ms fs) q l b w) s c ∧
        TP tp s) fs)
      (ContC p lbl' lsize' i cx exe endPc R F fp ra tp c0 fs Ab pc' e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ))) := by
  have he2 := hTn x cn τ e hT
  obtain ⟨la', ls, hla', hls, hcla, hbl, hcls, rfl⟩ := insts_newBuf hi
  cases ok_inj (hla.symm.trans hla')
  have hWls :=
    hAW c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpt la ls kk hla hls hcla hbl hcls
  have s3 := nbStore_seg (ms1 := ms' fs) (i := i) (c0 := c0) (fs := fs) hf h1 h16 hF hR hal hlo hhi lcx.prog
    he2 hfr hlbl hz hls (hCd _ _ hcls) (hWls lbl' lsize' hlbl hz) hIt hIc hlb
  refine ((SegWS.liftS fs s3 hW₀).mono_pre ?_).mono_post ?_
  · rintro s c fs' ⟨⟨hA, ht⟩, hfs⟩
    refine ⟨?_, hfs⟩
    have hL := at_leave (P := fun σC => ∃ c, nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
        (pc + Int64.ofNat (4 * (directives la).length)) (oF cx)
        (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
          (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)) σC c ∧
        (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label (ms fs) q .e).J
          (enter (-(cx.frame : Int)) σC) c) rfl
      (fun m hm => ⟨hF' m hm, by
        obtain ⟨mC, σC, c, hAb, hJ, hN, hK⟩ := hctx m hm
        exact ⟨mC, σC, _, hK, hAb, c, hJ, hN⟩⟩) hA
    obtain ⟨he, hn, hd, hpc, σ, hAs, hFm, σx, σC, ⟨ini, old, hc, hx0, hb, hold, -⟩,
      ⟨c', ⟨σ0, hJ1, hσC⟩, hc', -, h30, -⟩, rfl⟩ := hL
    have hra : Int64.ofBitVec q.ra = pc + Int64.ofNat (4 * (directives la).length) + 4 := by
      rw [← h30, hσC]
      erw [blD_run]
      simp only [Reg64s.setXReg]
      exact int64_ofBitVec_toBitVec _
    refine ⟨he, hn, hd, by rw [← hra]; exact hpc, _, hAs, hFm, ⟨q, hq⟩, ⟨σC, hc' ▸ ⟨σ0, hJ1, hσC⟩, ?_⟩,
      l, ini, old, hc, hx0.trans hb, hold, ⟨by decide, b, by simp [Scc.Sem.wordAddr, hl'], hx0.symm ▸ rfl⟩, hkz,
      hAs.regs ▸ ht⟩
    intro k _ hk
    simp only [leave]
    rw [ite_eq_right hk]
  · rintro s c fs' ⟨h, rfl⟩
    exact .inl ⟨rfl, h⟩

end Main

/-- info: 'Spike.Lib.LowerA64.insts_newBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.insts_newBuf

/-- info: 'Spike.Lib.LowerA64.getArgs_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.getArgs_three

/-- info: 'Spike.Lib.LowerA64.args3_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.args3_step

/-- info: 'Spike.Lib.LowerA64.okBlk_args3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.okBlk_args3

/-- info: 'Spike.Lib.LowerA64.args3_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.args3_ne_nil

/-- info: 'Spike.Lib.LowerA64.callOK_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callOK_tpXa

/-- info: 'Spike.Lib.LowerA64.callOK_untpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callOK_untpXa

/-- info: 'Spike.Lib.LowerA64.allocW_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.allocW_tpXa

/-- info: 'Spike.Lib.LowerA64.nbArgs_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.nbArgs_seg

/-- info: 'Spike.Lib.LowerA64.nbCall_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.nbCall_seg

/-- info: 'Spike.Lib.LowerA64.nbStore_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.nbStore_seg

/-- info: 'Spike.Lib.LowerA64.nbRet_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.nbRet_seg

/-- info: 'Spike.Lib.LowerA64.htot_newBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.htot_newBuf

/-- info: 'Spike.Lib.LowerA64.nbJcOf_nbJ1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.nbJcOf_nbJ1

/-- info: 'Spike.Lib.LowerA64.newBufC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.newBufC_of

/-- info: 'Spike.Lib.LowerA64.AllocW2.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.AllocW2.store

/-- info: 'Spike.Lib.LowerA64.AllocW2At.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.AllocW2At.store

/-- info: 'Spike.Lib.LowerA64.newBufC_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.newBufC_tail

end Spike.Lib.LowerA64
