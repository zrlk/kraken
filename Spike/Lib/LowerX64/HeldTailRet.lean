/-
**The held return tail's per-state facts at the callee's `ret`** (x86-64; the twin of
`Spike/Lib/LowerA64/HeldTailRet.lean`):
`HeldS`'s `Ret0` (`Spike/Lib/LowerX64/HeldTail.lean`) at a held callee's
`ret a`, from the word its return lands in the frame's result: a literal or
`unit` reads nothing, a variable's one word is the result register's.

- `ret0_of_evalAt`: `Ret0` from `a`'s value and its word at a register;
- `ret0_of_frameStep`: `Ret0` from the return's landing, the frame's
  result `f.x` bound to the word at a register;
- `wordRep_rax`, `ret0_of_rax`: the word at `%rax` from the abstract state;
- `lookup_of_nodeJE`, `ret0_of_retCP2`: at the result's store's node
  (`retCP2`), the frame's result placed as the stored register;
- `RetReg`, `nodeW_ret0`, `blkW_ret0`: `Ret0` along the tail's nodes and
  blocks that keep the result register.
-/
import Spike.Lib.LowerX64.HeldTail
import Spike.Lib.LowerX64.CallC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Scc.Sem (ValRep)
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA

/-- **`Ret0` at a held callee's `ret a`** from its value: a literal or `unit`
reads nothing; a variable's one word `w` represented at the place `pl`. -/
theorem ret0_of_evalAt {lbl : Lbl} {s : State} {c : Ctl} {a : At} {t : Ty} {w : TermRun.Word}
    (hc : c.term = .ret a) (ha : TermRun.evalAt c.env a = some (t, [w]))
    {pl : Place (machine (kernel 1)).I.RegId} (hr : WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val) :
    Ret0 lbl s c := by
  cases a with
  | var x => exact .inr ⟨x, t, w, pl, hc, ha, hr⟩
  | lit n => exact .inl (by rw [hc]; rfl)
  | unit => exact .inl (by rw [hc]; rfl)

/-- **`Ret0` at a held callee's `ret a` from the pair its return lands at**:
the frame's result `f.x` at the landing bound to one word `w` (`hl`; the
return's value) represented at the place `pl`. -/
theorem ret0_of_frameStep {p : Prog} {lbl : Lbl} {s : State} {c cR : Ctl} {f : TermRun.Frame}
    {fs : List TermRun.Frame} {a : At} (hc : c.term = .ret a) (hst : FrameStep p (c, f :: fs) (cR, fs))
    {ty : Ty} {w : TermRun.Word} (hl : TermRun.lookupE cR.env f.x = some (ty, [w]))
    {pl : Place (machine (kernel 1)).I.RegId} (hr : WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val) :
    Ret0 lbl s c := by
  cases hst with
  | @ret _ _ _ a' t ws hc' _ ha =>
    rw [hc] at hc'
    cases hc'
    simp only [TermRun.lookupE, List.find?_cons, beq_self_eq_true, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hl
    obtain ⟨-, rfl⟩ := hl
    exact ret0_of_evalAt hc ha hr

/-- **The result register's word** (`%rax`) from the abstract state: a
word represented by its value is represented at the register. -/
theorem wordRep_rax {R : Spike.Lib.Region} {o : Spike.Lib.X64.SO} {s : State} {σ : Spike.Lib.X64.AS}
    (hA : Spike.Lib.X64.Abs R o s.st.1 σ) {lbl : Lbl} {w : WeakMem.Val} (hv : ValRep lbl w (σ.regs.get64 .rax).toNat) :
    WordPlaceRep (machine (kernel 1)) lbl s (.one (.reg (.r .rax))) w := by
  have hx : Scc.Sem.X64.regVal s (.r .rax) = σ.regs.get64 .rax := by
    show s.st.1.regs.rax.toBitVec = _
    rw [hA.regs]; rfl
  exact ⟨_, congrArg (fun b : BitVec 64 => some b.toNat) hx, hv⟩

/-- **`Ret0` at a held callee's `ret a` from the result register**: the
return lands with the frame's result `f.x` bound to one word `w`, which the
abstract state's `%rax` represents. -/
theorem ret0_of_rax {p : Prog} {lbl : Lbl} {s : State} {c cR : Ctl} {f : TermRun.Frame}
    {fs : List TermRun.Frame} {a : At} (hc : c.term = .ret a) (hst : FrameStep p (c, f :: fs) (cR, fs))
    {ty : Ty} {w : TermRun.Word} (hl : TermRun.lookupE cR.env f.x = some (ty, [w]))
    {R : Spike.Lib.Region} {o : Spike.Lib.X64.SO} {σ : Spike.Lib.X64.AS} (hA : Spike.Lib.X64.Abs R o s.st.1 σ)
    (hv : ValRep lbl w.val (σ.regs.get64 .rax).toNat) : Ret0 lbl s c :=
  ret0_of_frameStep hc hst hl (wordRep_rax hA hv)

/-! ## At the result's store -/

/-- **A variable placed in one register operand reads the stored result**:
at a node whose cells are `sl` with the result `v` stored at the register's
offset (`hrs`), a variable placed as that operand (`hx`) is bound to one word
`v` represents. -/
theorem lookup_of_nodeJE {lbl : Lbl} {rs : Scc.IR.Reg → Option Int} {e : Expr} {s : Spike.Lib.Form.SEnv}
    {sl : Int → BitVec 64} {off : Int} {v : BitVec 64} {c : Ctl}
    (hJ : Spike.Lib.Form.NodeJE lbl rs e s (Spike.Lib.upd sl off v) c) {x : String} {t : Ty} {r : Scc.IR.Reg}
    (hx : Spike.Lib.Form.lookupS s x = some (t, [.one (.reg r)])) (hrs : rs r = some off) :
    ∃ ty w, TermRun.lookupE c.env x = some (ty, [w]) ∧ ValRep lbl w.val v.toNat := by
  obtain ⟨-, -, hs⟩ := hJ
  obtain ⟨ty, ws, hl, -, hw⟩ := hs.lookup hx
  match ws, hw with
  | [w], ⟨⟨vv, hvv, hrep⟩, _⟩ =>
    simp only [Spike.Lib.Form.opdVal, hrs, Option.map_some, Spike.Lib.upd_apply, if_pos rfl,
      Option.some.injEq] at hvv
    exact ⟨ty, w, hl, hvv ▸ hrep⟩

/-- **`Ret0` at a held callee's `ret a` at the result's store** (`retCP2`,
the store of `%rax`, the frame's result `f.x`): the return lands at the
store's node, whose symbolic environment places `f.x` as a register
operand at the store's offset (`hx`, `hrs`), so `%rax` holds its word. -/
theorem ret0_of_retCP2 {p : Prog} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}
    {F : MachineData → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    {fs : List TermRun.Frame} {Q : Ctl → Prop} {pcR : Int64} {e : Expr} {s : Spike.Lib.Form.SEnv} {off : Int}
    {st : State} {c cR : Ctl} {f : TermRun.Frame} {a : At} (hc : c.term = .ret a)
    (hst : FrameStep p (c, f :: fs) (cR, fs))
    (hA : Spike.Lib.X64.At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off) st cR)
    {t : Ty} {r : Scc.IR.Reg} (hx : Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]))
    (hrs : rsOf fr r = some off) : Ret0 lbl st c := by
  obtain ⟨-, -, -, -, σ, hAb, -, hJ, -⟩ := hA
  obtain ⟨ty, w, hl, hv⟩ := lookup_of_nodeJE hJ hx hrs
  exact ret0_of_rax hc hst hl hAb hv

/-! ## Along the tail -/

/-- **A node's state holds a held callee's result in the result register**:
the control a callee's `ret a`, its return landing with the frame's result
bound to one word the abstract state's result register represents. -/
def RetReg (p : Prog) (lbl : Lbl) (σ : Spike.Lib.X64.AS) (c : Ctl) : Prop :=
  ∃ a f fs cR ty w, c.term = .ret a ∧ FrameStep p (c, f :: fs) (cR, fs) ∧
    TermRun.lookupE cR.env f.x = some (ty, [w]) ∧ ValRep lbl w.val (σ.regs.get64 .rax).toNat

/-- **A node's states are `Ret0`** where its invariant holds the result in
the result register (`RetReg`). -/
theorem nodeW_ret0 {p : Prog} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}
    {F : MachineData → Prop} {n : Spike.Lib.X64.ND} (hJ : ∀ σ c, n.J σ c → RetReg p lbl σ c) :
    Spike.Lib.X64.NodeW (Ret0 lbl) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hJn⟩
  obtain ⟨a, f, fs, cR, ty, w, hc, hst, hl, hv⟩ := hJ σ c hJn
  exact ⟨ret0_of_rax hc hst hl hA hv, fun _ h => h⟩

/-- **A block's states are `Ret0`** where the node's invariant holds the
result in the result register (`RetReg`) and the block's instructions
before each state leave the register as it was (`hx`). -/
theorem blkW_ret0 {p : Prog} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}
    {F : MachineData → Prop} {n : Spike.Lib.X64.ND} {blk : List (Directive × Nat)}
    (hJ : ∀ σ c, n.J σ c → RetReg p lbl σ c)
    (hx : ∀ σ k, k < blk.length →
      (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rax =
        σ.regs.get64 .rax) :
    Spike.Lib.X64.BlkW (Ret0 lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJn k hk m hA' _
  obtain ⟨a, f, fs, cR, ty, w, hc, hst, hl, hv⟩ := hJ σ c hJn
  refine ⟨ret0_of_rax hc hst hl hA' ?_, fun _ h => h⟩
  rw [hx σ k hk]; exact hv

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.ret0_of_frameStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ret0_of_frameStep

/-- info: 'Spike.Lib.LowerX64.blkW_ret0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_ret0

/-- info: 'Spike.Lib.LowerX64.ret0_of_rax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ret0_of_rax

/-- info: 'Spike.Lib.LowerX64.ret0_of_retCP2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ret0_of_retCP2
