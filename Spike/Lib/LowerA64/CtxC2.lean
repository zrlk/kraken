/-
**The contexts at a call of an `Accepted2` body** (AArch64): `CtxC.lean`'s
`framesPlaced_calleeF`, `envSmall_calleeF`, `CtxB.callF` from the callee's
frame condition `CalleeF2` (`Spike/Lib/LowerA64/CallC2.lean`), whose caller
words may be locatives (a buffer's base and offset) and whose environment is
small by the walk's facts (`EnvQ`) rather than numeric. The twin of
`Spike/Lib/LowerX64/CtxC2.lean`; a separate file since `CtxC` is below
`CallC2` in the imports.

- `slotPlacedI_of_slotRepAt`: `slotPlacedI_of_slotRep` at the immediates of
  any term `t` (at a call, the continuation);
- `framesPlaced_calleeF2`: the caller's frame placed from the node
  invariant with the continuation's register bases (`placedPf_of_slotRep`),
  kept by the callee, on the caller's frames;
- `envSmall_calleeF2`: `EnvQ`'s `EnvSmall`;
- `CtxB.callF2`: `CtxB.call` from `CalleeF2`.
-/
import Spike.Lib.LowerA64.CtxC
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.A64PlacedSlot

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (CallerCells StackOff limA)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (FramesPlacedInI)

section CallF2

open Spike.Lib.A64ConsumerS (SlotPlacedI placedPf_of_slotRep)
open Spike.Lib.Form (SEnv lookupS WordPl)

variable {p : Prog} {tbl : List Scc.Cert.NeedA64.Row} {Λ : Scc.Sem.Layout} {lbl : Lbl}
  {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2} {rS : Scc.Sem.Range}

/-- **A control placed in a slot file whose slots are cells of `A`, at a
term `t`'s immediates** (`slotPlacedI_of_slotRep` at `t`, not the
control's term: at a call, the continuation): slot `k` the cell at
`addr k`, loading `sl k` (`hcell`). -/
theorem slotPlacedI_of_slotRepAt {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} {s : State}
    {A : Nat → Prop} {addr : Int → BitVec 64} {t : Expr} (h : SlotRepAt (fun _ => Λ.imms t) lbl rs sl c)
    (hcell : ∀ r k, rs r = some k → Scc.Sem.A64.privLoad s (addr k) = some (sl k))
    (hA : ∀ r k, rs r = some k → A (addr k).toNat) :
    SlotPlacedI Λ lbl s c A t := by
  obtain ⟨envm, hrep, htot, hpl, himm⟩ := placedPf_of_slotRep (pf := fun k => .slot (addr k).toNat) h
    (fun r k hk => by
      show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (addr k).toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hcell r k hk]; rfl)
  refine ⟨envm, hrep, htot, fun x k wp hem q hq => ?_, himm⟩
  obtain ⟨r, k', hk', rfl⟩ := hpl x k wp hem q hq
  exact ⟨_, rfl, hA r k' hk'⟩

/-- **The frames at the callee's entry placed** under its frame condition
at a call of an `Accepted2` body (`CalleeF2` at the layout's immediates;
`framesPlaced_calleeF` with the caller's words locatives too): the
caller's frame `frm` placed in its slots from the node invariant at the
call with the continuation's register bases (`slotPlacedI_of_slotRepAt`),
kept by the callee, on the caller's frames `fs` placed under the caller's
frame condition. -/
theorem framesPlaced_calleeF2 {cx : FnCtx} (hf : FrameOk cx)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF2 p lbl lsize cx R F D fp ra Λ.imms T q frm F')
    (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A) :
    ∀ s : State, F' s.st.1 → ∃ A, FramesPlacedInI Λ lbl s (frm :: fs) A := by
  intro s hm
  obtain ⟨A2, h2⟩ := hFP s (hCF _ hm).1
  obtain ⟨-, -, mC, σC, c, t, sv, hA, hk, hct, -, hj, -, -, htot, hlb, himm⟩ := hCF _ hm
  obtain ⟨x, g, a, e, d, ty, ws, -, -, -, -, rfl⟩ := id hct
  have hout : ∀ r k, rsOf cx r = some k →
      R.Off k ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (k - (-(cx.frame : Int))) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3, -⟩ := rsOf_cell hf hk
    exact frame_outA hlo hhi hD0 hk1 hk2 (by omega)
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf cx r = some k ∧ a = (R.addr k).toNat
  let sC : State := { s with st := (mC, s.st.2) }
  have hfv : ∀ y ∈ Scc.Sem.exprFv (Expr.let_ x (.atom .unit) e), y ∈ Scc.Sem.exprFv e ∧ y ≠ x := by
    intro y hy
    simpa [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars] using hy
  have hsr : SlotRepAt (fun _ => Λ.imms e) lbl (rsOf cx) σC.slot { c with term := .let_ x (.atom .unit) e } := by
    refine SlotRepAt.of_srepE (s := sv.filter (·.1 != x)) ?_ ?_ ?_ ?_
    · intro y ty' pls hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact hj.2.2 y ty' pls hl
    · intro y hy
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2]
      exact htot y hy.1 hy.2
    · intro y hy ty' pls hl b o hb
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2] at hl
      exact hlb y hy.1 hy.2 ty' pls hl b o hb
    · intro y k v hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact himm y k v hy hl
  have hsp : SlotPlacedI Λ lbl sC { c with term := .let_ x (.atom .unit) e } A1 e := by
    refine slotPlacedI_of_slotRepAt (addr := R.addr) hsr ?_ (fun r k hk => ⟨r, k, hk, rfl⟩)
    intro r k hk
    obtain ⟨jj, hl, hv⟩ := hA.slot k (hout r k hk).1
    show (mC.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64) = _
    rw [hl, Option.map_some, hv]
  have h1 : FramesPlacedInI Λ lbl sC [⟨x, e, c.env, [], d.retTy⟩] A1 :=
    Spike.Lib.A64ConsumerS.FramesPlacedInI.push hsp (Spike.Lib.A64ConsumerS.FramesPlacedInI.nil A1) rfl rfl rfl rfl
  have h1' : FramesPlacedInI Λ lbl s [⟨x, e, c.env, [], d.retTy⟩] A1 :=
    h1.of_cKept (s := sC) hk fun a ⟨r, k, hk', ha⟩ => ⟨k, (hout r k hk').1, (hout r k hk').2, ha⟩
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1'.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

/-- **The caller's frame's environment is small** under the callee's frame
condition at a call of an `Accepted2` body (`CalleeF2`'s `EnvQ`). -/
theorem envSmall_calleeF2 {cx : FnCtx} {R : Region} {F : MachineData → Prop} {D : Int}
    {fp ra : BitVec 64} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop} (hCF : CalleeF2 p lbl lsize cx R F D fp ra i T q frm F') :
    ∀ m, F' m → EnvSmall frm.env := by
  intro m hm
  obtain ⟨-, -, mC, σC, c, t, sv, -, -, hct, -, -, ⟨lits, cs, bufs, hq⟩, -⟩ := hCF m hm
  obtain ⟨x, g, a, e, d, ty, ws, -, -, -, -, rfl⟩ := hct
  exact hq.2.1

/-- **A call of an `Accepted2` body keeps the context, from the callee's
frame condition** (`CtxB.callF` at `CalleeF2`; `framesPlaced_calleeF2`,
`envSmall_calleeF2`). -/
theorem CtxB.callF2 {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {tp : UInt64}
    (hc : CtxB p tbl Λ lbl ms rS j R F fs tp) {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D)
    {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (R.callee (-(cx.frame : Int)) (-D) 0) F')
    (hCF : CalleeF2 p lbl lsize cx R F D fp ra Λ.imms T q frm F')
    {j' : Nat}
    (hroom : ∀ d, p[j']? = some d → NeedRoomA tbl (Scc.Lower.Names.user d.name) 48 (-D))
    (hlim : ∀ d, p[j']? = some d →
      LimRoomA tbl (Scc.Lower.Names.user d.name) ((ms []).G ⟨limA tp, 8⟩) (R.base.toNat - cx.frame)) :
    CtxB p tbl Λ lbl ms rS j' (R.callee (-(cx.frame : Int)) (-D) 0) F' (frm :: fs) tp := by
  have hhi := hc.hhi
  have hpos : 0 < cx.frame := by
    have := align16_mod (8 * cx.slots.length + 16)
    have := le_align16 (8 * cx.slots.length + 16)
    unfold FrameOk at hf
    omega
  exact hc.call h16 hpos hD0 hD8 hlo hF' (fun m hm => ⟨(hCF m hm).1, (hCF m hm).2.1⟩) hroom hlim
    (framesPlaced_calleeF2 hf hCF hlo (by omega) hD0 hc.hFP) (envSmall_calleeF2 hCF)

end CallF2

/-- info: 'Spike.Lib.LowerA64.slotPlacedI_of_slotRepAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.slotPlacedI_of_slotRepAt

/-- info: 'Spike.Lib.LowerA64.framesPlaced_calleeF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.framesPlaced_calleeF2

/-- info: 'Spike.Lib.LowerA64.envSmall_calleeF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.envSmall_calleeF2

/-- info: 'Spike.Lib.LowerA64.CtxB.callF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CtxB.callF2

end Spike.Lib.LowerA64
