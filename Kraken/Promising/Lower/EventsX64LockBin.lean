/-
**`lock op %r, (m)` (`lockBin`) on the fuel-free
machine.** The `lockBin` twin of
`Lower/EventsX64Inf.lean`'s `instrSemInf_xadd`.

Kraken's x64 has `lockBin` (`X64/Syntax.lean`: `lock add/sub/and/or/xor` on a
memory destination; `X64/Semantics.lean` `.lockBin`): one locked RMW
(`rmwK .acqRel`) writing `op.eval old src`, then the flags. The logic
operations leave `AF` architecturally undefined, so the tree after the RMW is
a two-way `choose` (`Effects.undefined` at `Bool`, `Promising/X64.lean`
`toEv`), whatever `op` is (the arithmetic ones ignore the choice). The event
shape is still **a single RMW**: `instrSemInf_lockBin` is
`instrSemInf_rmw_at`'s right-hand side under one more existential, the `AF`
bit `af`. The old value is dead (only the flags see it), which is the
WeakCore `fetch op` row with an unused result.

- `exec_lockBin_reg`: the tree at a `lock op %r, (m)` cell, `m` not in `dmem`.
- `run_rmw_choose_iff` (ISA-neutral): a run of an RMW whose continuation is a
  finite choice of `done`s is a run of the RMW with one branch.
- `instrSemInf_lockBin`.
-/
import Kraken.Promising.Lower.EventsX64Inf

namespace Kraken.Promising.Lower

open Kraken.Promising

variable {I : ISA} (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **An RMW followed by a finite choice** of `done`s: a run is a run of the
RMW followed by one branch. -/
theorem run_rmw_choose_iff {σ : Type} {c c' : Ctx} {k : RmwKind} {noRet : Bool} {l : Loc}
    {op : Val → Option Val} {n : Nat} {f : Val → Fin n → σ} {st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.rmw k noRet l op fun v => .choose n fun i => .done (f v i)) ↔
      ∃ i, .ok (st, c') ∈ runTree A tid iv c (.rmw k noRet l op fun v => .done (f v i)) := by
  simp only [runTree.eq_7, List.mem_flatMap]
  constructor
  · rintro ⟨⟨tr, old, c1⟩, hx, h⟩
    dsimp only at h
    cases hop : op old with
    | none =>
      simp only [hop] at h
      obtain ⟨i, hi⟩ := (run_choose_iff A tid iv).mp h
      exact ⟨i, ⟨tr, old, c1⟩, hx, by dsimp only; simp only [hop]; exact hi⟩
    | some new =>
      simp only [hop, List.mem_flatMap] at h
      obtain ⟨c2, h2, h⟩ := h
      obtain ⟨i, hi⟩ := (run_choose_iff A tid iv).mp h
      exact ⟨i, ⟨tr, old, c1⟩, hx, by dsimp only; simp only [hop, List.mem_flatMap]; exact ⟨c2, h2, hi⟩⟩
  · rintro ⟨i, ⟨tr, old, c1⟩, hx, h⟩
    refine ⟨⟨tr, old, c1⟩, hx, ?_⟩
    dsimp only at h ⊢
    cases hop : op old with
    | none =>
      simp only [hop] at h ⊢
      exact (run_choose_iff A tid iv).mpr ⟨i, h⟩
    | some new =>
      simp only [hop, List.mem_flatMap] at h ⊢
      obtain ⟨c2, h2, hi⟩ := h
      exact ⟨c2, h2, (run_choose_iff A tid iv).mpr ⟨i, hi⟩⟩

end Kraken.Promising.Lower

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- Read the cell through `exec_of_cellAt` and unfold it (`EventsX64.lean`'s
local `cell`, repeated: local macros do not cross files). -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  try simp only [rspOf, Reg64s.get64] at *
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, Width.bytesv, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-- The state after `lock op %r, (m)` read `old`, with `AF` bit `af`. -/
abbrev lockBinPost (st : State) (sz : Nat) (op : LockBinOp) (r : Reg .W64) (old : BitVec 64) (af : Bool) : State :=
  after st sz { st.st.1 with
    status := op.status old (st.st.1.regs.get r) (op.eval old (st.st.1.regs.get r)) af }

/-- **`lock op %r, (m)`**, address unmapped in `dmem`: one locked RMW
writing `op.eval old r`, then a choice of the undefined `AF` bit. -/
theorem exec_lockBin_reg {st : State} {sz : Nat} {op : LockBinOp} {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt st (op64 (.lockBin op m (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l =>
      .rmw .acqRel false l (fun old => some ((op.eval (old.setWidth 64) (st.st.1.regs.get r)).setWidth 128))
        fun v => .choose 2 fun i => .done (lockBinPost st sz op r (v.setWidth 64) (i.val == 1))) := by
  cell hc [ha, hdm]

variable (A : Arch) (tid : Nat) {c c' : Config isa} {t : Thread isa}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`lock op %r, (m)`**: one locked RMW at `⟨a, 8⟩` writing
`op.eval old r`; the old value reaches only the flags, with the undefined
`AF` bit `af` (`instrSemInf_xadd`'s shape, one more existential). -/
theorem instrSemInf_lockBin {op : LockBinOp} {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt (stOf t) (op64 (.lockBin op m (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ af : Bool, ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, 8⟩ false ∧
      ((some ((op.eval (old.setWidth 64) ((stOf t).st.1.regs.get r)).setWidth 128) = none ∧
          cf = rmwFenceOpt A c1) ∨
       (∃ new c2, some ((op.eval (old.setWidth 64) ((stOf t).st.1.regs.get r)).setWidth 128) = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, 8⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, 8⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (lockBinPost (stOf t) sz op r (old.setWidth 64) af) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem := by
  rw [instrSemInf_iff_of_exec A tid ht (by rw [exec_lockBin_reg hc ha hdm, access_agrees hag])]
  have hf := fun st c1 => run_rmw_choose_iff A tid (ivOf t) (c := ctx0 tid t c.mem) (c' := c1) (st := st)
    (k := .acqRel) (noRet := false) (l := ⟨a, 8⟩)
    (op := fun old => some ((op.eval (old.setWidth 64) ((stOf t).st.1.regs.get r)).setWidth 128))
    (f := fun v (i : Fin 2) => lockBinPost (stOf t) sz op r (v.setWidth 64) (i.val == 1))
  constructor
  · rintro ⟨th, mem', ⟨st, cf, hr, hth, rfl⟩, hcert, rfl⟩
    obtain ⟨i, hr⟩ := (hf _ _).mp hr
    obtain ⟨tr, old, c1, hx, rfl, h⟩ := (run_rmw_iff A tid _).mp hr
    exact ⟨i.val == 1, tr, old, c1, cf, th, hx, h, hth, hcert, rfl⟩
  · rintro ⟨af, tr, old, c1, cf, th, hx, h, hth, hcert, rfl⟩
    refine ⟨th, cf.mem, ⟨_, cf, (hf _ _).mpr ⟨if af then 1 else 0, (run_rmw_iff A tid _).mpr ⟨tr, old, c1, hx, ?_, h⟩⟩,
      hth, rfl⟩, hcert, rfl⟩
    cases af <;> rfl

end Kraken.Promising.Lower.X64
