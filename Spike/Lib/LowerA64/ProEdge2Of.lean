/-
**The prologue's edge into a compiled block's body** (AArch64): `ProEdge2`
(`Spike/Lib/LowerA64/ProgC2.lean`) from the caller's facts at the entry,
for any number of parameter words (`ParamSpill` of `Spike/Lib/LowerA64/FnC.lean`
generalised from one word).

- `SpillAt`, `SpillsAt`, `ParamSpillN`: the prologue's parameter spill
  `ps` for the parameter registers `prs`: the `k`th register stored from
  `argRegs[k]` at its cell (`rsOf`), below the saved pair, a cell of the
  frame;
- `paramSpillN_of_spills`: `spills`' result is one;
- `stSlots_off`, `stSlots_paramN`: after the stores, a cell of none of them
  unchanged, and the `k`th register's cell the entry's `argRegs[k]`;
- `frRegs_arg`: the check and the frame's set-up keep the argument
  registers;
- `proEdge2_of`: `ProEdge2` at an entry invariant `J` whose states give the
  stack limit's facts, the saved pair `fp`, `ra`, the thread pointer `tp`,
  the ghost's local run, and the body's entry node's source facts at every
  slot map with the parameter registers' cells the argument registers;
  `proEdge2_ofSpills` at a compiled block's `spills` (`paramsR`).
-/
import Spike.Lib.LowerA64.ProgC2
import Spike.Lib.Src.ParamsNodup

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode

/-- **One parameter's store** (`ParamSpillN`'s): the register `q.1` stored
from `q.2` at offset `s.2` from the new `sp`, its cell `-frame + s.2`
(`rsOf cx`), below the saved pair and a cell of the frame. -/
def SpillAt (cx : FnCtx) (q : Scc.IR.Reg × XReg) (s : XReg × Int64) : Prop :=
  s.1 = q.2 ∧ rsOf cx q.1 = some (-(cx.frame : Int) + s.2.toInt) ∧ -(cx.frame : Int) + s.2.toInt ≤ -24 ∧
    offOk (-(cx.frame : Int)) 0 (-(cx.frame : Int) + s.2.toInt) = true

/-- `SpillAt` pairwise along two lists of the same length. -/
def SpillsAt (cx : FnCtx) : List (Scc.IR.Reg × XReg) → List (XReg × Int64) → Prop
  | [], [] => True
  | q :: l, s :: ps => SpillAt cx q s ∧ SpillsAt cx l ps
  | _, _ => False

/-- **The prologue's parameter spill** `ps` for the parameter registers
`prs` of a function with frame `cx`, any number of them up to
`argRegs.length`: the `k`th register `prs[k]` stored from `argRegs[k]`
(`SpillAt`). -/
def ParamSpillN (cx : FnCtx) (ps : List (XReg × Int64)) (prs : List Scc.IR.Reg) : Prop :=
  prs.length ≤ argRegs.length ∧ SpillsAt cx (prs.zip argRegs) ps

/-- A successful `mapM` in `Option`, element by element: each result
`SpillAt` its argument when each successful `f` is. -/
theorem spillsAt_of_mapM {cx : FnCtx} {f : Scc.IR.Reg × XReg → Option (XReg × Int64)}
    (hf : ∀ q s, f q = some s → SpillAt cx q s) :
    ∀ {l : List (Scc.IR.Reg × XReg)} {ys : List (XReg × Int64)}, l.mapM f = some ys → SpillsAt cx l ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; trivial
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some ys' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        exact ⟨hf a b ha, spillsAt_of_mapM hf hl⟩

/-- **`spills`' result is a `ParamSpillN`** (at a frame of `FrameOk`, at
most 4095 bytes, 16-aligned). -/
theorem paramSpillN_of_spills {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {prs : List Scc.IR.Reg} {ps : List (XReg × Int64)}
    (h : Scc.Cert.Code1A64.spills cx prs = some ps) : ParamSpillN cx ps prs := by
  unfold Scc.Cert.Code1A64.spills at h
  split at h
  · rename_i hle
    refine ⟨hle, spillsAt_of_mapM (fun q s hq => ?_) h⟩
    obtain ⟨pr, r⟩ := q
    cases ho : cx.slotOff pr with
    | error e => simp [ho, Except.toOption] at hq
    | ok o =>
      simp only [ho, Except.toOption, Option.map_some, Option.some.injEq] at hq
      subst hq
      obtain ⟨h0, h8, hle'⟩ := slotOff_bounds hf ho
      have hoo : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [rsOf, ho, hoo, Option.some.injEq]; omega
      · simp only [hoo]; omega
      · simp only [hoo, offOk, decide_eq_true_eq]; omega
  · cases h

/-- **After the parameters' stores, a cell none of them writes is
unchanged.** -/
theorem stSlots_off (sp : Int) (regs : Reg64s) :
    ∀ (ps : List (XReg × Int64)) (sl : Int → BitVec 64) (k : Int), (∀ q ∈ ps, sp + q.2.toInt ≠ k) →
      stSlots sp regs ps sl k = sl k
  | [], _, _, _ => rfl
  | q :: ps, sl, k, h => by
    simp only [stSlots]
    rw [stSlots_off sp regs ps _ k fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]
    have := h q List.mem_cons_self
    simp [upd_apply, Ne.symm this]

/-- Every store of `SpillsAt` is `SpillAt` some register of `l`. -/
theorem SpillsAt.mem {cx : FnCtx} :
    ∀ {l : List (Scc.IR.Reg × XReg)} {ps : List (XReg × Int64)}, SpillsAt cx l ps →
      ∀ s ∈ ps, ∃ q ∈ l, SpillAt cx q s
  | [], [], _, s, hs => absurd hs List.not_mem_nil
  | q :: l, s' :: ps, ⟨hq, hr⟩, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨q, List.mem_cons_self, hq⟩
    · obtain ⟨q', hq', h'⟩ := SpillsAt.mem hr s hs
      exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- **After a `SpillsAt`'s stores, every parameter register's cell holds
its argument register**, the registers distinct. -/
theorem stSlots_paramN {cx : FnCtx} (regs : Reg64s) :
    ∀ {l : List (Scc.IR.Reg × XReg)} {ps : List (XReg × Int64)}, SpillsAt cx l ps → (l.map (·.1)).Nodup →
      ∀ (sl : Int → BitVec 64), ∀ q ∈ l, ∀ k, rsOf cx q.1 = some k →
        stSlots (-(cx.frame : Int)) regs ps sl k = (regs.getXReg q.2).toBitVec
  | [], [], _, _, _, q, hq, _, _ => absurd hq List.not_mem_nil
  | a :: l, s :: ps, ⟨hs, hrest⟩, hnd, sl, q, hq, k, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [stSlots]
    rcases List.mem_cons.1 hq with rfl | hq
    · obtain ⟨hs1, hrs, -, -⟩ := hs
      rw [hrs] at hk
      cases hk
      rw [stSlots_off]
      · simp [upd_apply, hs1]
      · intro s' hs' he
        obtain ⟨a', ha', -, hrs', -, -⟩ := hrest.mem s' hs'
        rw [he] at hrs'
        exact hnd.1 ⟨a', ha', rsOf_inj hrs' hrs⟩
    · exact stSlots_paramN regs hrest hnd.2 _ q hq k hk
  | [], _ :: _, h, _, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _, _ => h.elim

/-- The cells a `ParamSpillN`'s stores write are below the saved pair. -/
theorem ParamSpillN.le24 {cx : FnCtx} {ps : List (XReg × Int64)} {prs : List Scc.IR.Reg}
    (h : ParamSpillN cx ps prs) : ∀ q ∈ ps, -(cx.frame : Int) + q.2.toInt ≤ -24 := by
  intro q hq
  obtain ⟨_, _, -, -, h24, -⟩ := h.2.mem q hq
  exact h24

/-- A `ParamSpillN`'s stores are cells of the frame (`prologue_seg_ofW`'s
`hps`). -/
theorem ParamSpillN.hps {cx : FnCtx} (h1 : cx.frame ≤ 4095) {ps : List (XReg × Int64)} {prs : List Scc.IR.Reg}
    (h : ParamSpillN cx ps prs) :
    ∀ q ∈ ps, offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true := by
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  rw [hF64]
  intro q hq
  obtain ⟨_, _, -, -, -, hok⟩ := h.2.mem q hq
  exact hok

/-- **The check and the frame's set-up keep the argument registers.** -/
theorem frRegs_arg (Z : Int64) (v : BitVec 64) (σ : AS) :
    ∀ r ∈ argRegs, (frRegs Z (ldStep .X10 v { σ with regs := chkRegs Z σ.regs }).regs).getXReg r =
      σ.regs.getXReg r := by
  intro r hr
  simp only [argRegs, xregs, List.take, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [frRegs, ldStep, chkRegs, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg]

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}

/-- **The prologue's edge into a compiled block's body** (`ProEdge2`) from
the entry's facts: at every state of `J`, the stack limit's facts, the
saved pair `fp`, `ra`, the thread pointer `tp`, the ghost's local run, and
at every slot map with the parameter registers `prs` (the spill's,
`ParamSpillN`, distinct) holding the argument registers and the saved pair,
the body's entry node's source facts (`NJB` from no known values or
buffers, `SlotRepAt`). -/
theorem proEdge2_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) {prs : List Scc.IR.Reg} (hsp : ParamSpillN c.cx c.ps prs)
    (hnd : prs.Nodup) {ms0 : MemSide isaLSE2} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64}
    {c0 : Ctl} {J : AS → Ctl → Prop}
    (hedge : ∀ σ c', J σ c' →
      (ms0.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        ms0.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, ms0.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt c.cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0 = tp ∧ LocalRun p c0 c' ∧
      ∀ sl : Int → BitVec 64,
        (∀ pr r, (pr, r) ∈ prs.zip argRegs → ∀ k, rsOf c.cx pr = some k → sl k = (σ.regs.getXReg r).toBitVec) →
        FrJ fp ra sl →
        (∃ L sm B, NJB p lbl (rsOf c.cx) c.lits [] [] L sm lsize B d.body (ofEnv2 c.env) sl c') ∧
          SlotRepAt i lbl (rsOf c.cx) sl c') :
    ProEdge2 p lbl lsize ms0 F c fp ra tp c0 J := by
  have h1 := c.h1
  have hF64 : (Int64.ofInt c.cx.frame).toInt = c.cx.frame := toInt_ofInt_small (by omega) (by omega)
  intro σ c' hJ
  obtain ⟨⟨hrt, hmp, hld, hG⟩, h29, h30, htp, hc0, hN⟩ := hedge σ c' hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' hr hsl => ?_⟩⟩
  have hfr : FrJ fp ra σ'.slot := by
    rw [hsl, hF64]
    have h16 := stSlots_off (-(c.cx.frame : Int)) σ'.regs c.ps (frSlot σ) (-16)
      fun q hq => by have := hsp.le24 q hq; omega
    have h8 := stSlots_off (-(c.cx.frame : Int)) σ'.regs c.ps (frSlot σ) (-8)
      fun q hq => by have := hsp.le24 q hq; omega
    rw [← h29, ← h30]
    exact ⟨h16.trans (frJ_frSlot σ).1, h8.trans (frJ_frSlot σ).2⟩
  have hpar : ∀ pr r, (pr, r) ∈ prs.zip argRegs → ∀ k, rsOf c.cx pr = some k →
      σ'.slot k = (σ.regs.getXReg r).toBitVec := by
    intro pr r hm k hk
    rw [hsl, hF64, stSlots_paramN σ'.regs hsp.2 (by rw [List.map_fst_zip hsp.1]; exact hnd) _ (pr, r) hm k hk, hr,
      frRegs_arg _ _ _ r (List.of_mem_zip hm).2]
  obtain ⟨hNJ, hrep⟩ := hN σ'.slot hpar hfr
  refine ⟨⟨hNJ, hfr, hc0, hrep⟩, ?_⟩
  rw [hr, tp_frRegs]; exact htp

/-- **`proEdge2_of` at a compiled block's spill** (`spills` at its
parameter registers `paramsR d na`, `paramSpillN_of_spills`,
`paramsR_nodup`). -/
theorem proEdge2_ofSpills {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) {na : Nat}
    (hs : Scc.Cert.Code1A64.spills c.cx (Spike.Lib.LowerShape.paramsR d na) = some c.ps)
    {ms0 : MemSide isaLSE2} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64}
    {c0 : Ctl} {J : AS → Ctl → Prop}
    (hedge : ∀ σ c', J σ c' →
      (ms0.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        ms0.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, ms0.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt c.cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0 = tp ∧ LocalRun p c0 c' ∧
      ∀ sl : Int → BitVec 64,
        (∀ pr r, (pr, r) ∈ (Spike.Lib.LowerShape.paramsR d na).zip argRegs → ∀ k, rsOf c.cx pr = some k →
          sl k = (σ.regs.getXReg r).toBitVec) →
        FrJ fp ra sl →
        (∃ L sm B, NJB p lbl (rsOf c.cx) c.lits [] [] L sm lsize B d.body (ofEnv2 c.env) sl c') ∧
          SlotRepAt i lbl (rsOf c.cx) sl c') :
    ProEdge2 p lbl lsize ms0 F c fp ra tp c0 J :=
  proEdge2_of c (paramSpillN_of_spills c.hf c.h1 c.h16 hs) (Spike.Lib.LowerShape.paramsR_nodup d na) hedge

end Edge

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.paramSpillN_of_spills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.paramSpillN_of_spills

/-- info: 'Spike.Lib.LowerA64.proEdge2_ofSpills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proEdge2_ofSpills

/-- info: 'Spike.Lib.LowerA64.proEdge2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proEdge2_of
