/-
**The contexts at a call of an `Accepted2` body** (x86-64): `CtxC.lean`'s
`framesPlaced_calleeF`, `envSmall_calleeF`, `CtxB.callF` under the callee's
frame condition at such a call (`CalleeF2`, `CallC2.lean`), whose caller's
environment may hold locatives (no `EnvNum`).

- `framesPlaced_calleeF2`: the caller's pushed frame placed from its slot
  representation (`placedPf_of_slotRep` at the caller's state, the
  locatives' register bases `CalleeF2`'s), kept by the callee, on the
  caller's frames;
- `envSmall_calleeF2`: the caller's environment small (`EnvQ`);
- `CtxB.callF2`: `CtxB.call` from `CalleeF2`.
-/
import Spike.Lib.LowerX64.CtxC
import Spike.Lib.LowerX64.CallC2
import Spike.Lib.X64PlacedSlot

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (CallerCells StackOff limA)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (FramesPlacedInI SlotPlacedI placedPf_of_slotRep)
open Spike.Lib.Form (SEnv lookupS)
open Spike.Lib.X64.Flow (CallTo)
open Spike.Lib.LowerNode (SlotRepAt EnvQ)

section Frames

variable {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : WeakMem.AllocLabel → Nat}

/-- **The frames at the callee's entry placed** under its frame condition
at a call of an `Accepted2` body (`CalleeF2` at the layout's immediates;
`framesPlaced_calleeF` with locatives): the caller's frame `frm` placed
from its slot representation at the caller's state (`placedPf_of_slotRep`,
its slots among its frame's cells, kept by the callee), on the caller's
frames `fs` placed under the caller's frame condition. -/
theorem framesPlaced_calleeF2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF2 p lbl lsize fr R F D fp ra Λ.imms T q frm F')
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A) :
    ∀ s : State, F' s.st.1 → ∃ A, FramesPlacedInI Λ lbl s (frm :: fs) A := by
  intro s hm
  obtain ⟨hFm, -, mC, σC, c, t, sv, hA, hk, hct, -, hj, -, -, htot, hlb, himm⟩ := hCF _ hm
  obtain ⟨A2, h2⟩ := hFP s hFm
  obtain ⟨x, g, a, e, d, ty, ws, -, -, -, -, rfl⟩ := id hct
  have hout : ∀ r k, rsOf fr r = some k →
      R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-D) 8).Off (k - (-(fr.size : Int) - 8)) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk
    exact frame_out hlo hhi hD0 hk2 (by omega) (by omega)
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf fr r = some k ∧ a = (R.addr k).toNat
  let sC : State := { s with st := (mC, s.st.2) }
  let c' : Ctl := { c with term := .let_ x (.atom .unit) e }
  have hfv : ∀ y ∈ Scc.Sem.exprFv c'.term, y ∈ Scc.Sem.exprFv e ∧ y ≠ x := by
    intro y hy
    simpa [c', Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars] using hy
  -- the caller's control at its continuation, placed in its slots
  have hsr : SlotRepAt (fun _ => Λ.imms e) lbl (rsOf fr) σC.slot c' := by
    refine SlotRepAt.of_srepE (s := sv.filter (·.1 != x)) (fun y ty' pls hl => ?_) (fun y hy => ?_)
      (fun y hy ty' pls hl => ?_) (fun y k v hl => ?_)
    · by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact hj.2.2 y ty' pls hl
    · obtain ⟨hy1, hy2⟩ := hfv y hy
      rw [lookupS_filter_ne _ hy2]
      exact htot y hy1 hy2
    · obtain ⟨hy1, hy2⟩ := hfv y hy
      rw [lookupS_filter_ne _ hy2] at hl
      exact hlb y hy1 hy2 ty' pls hl
    · by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact himm y k v hy hl
  obtain ⟨envm, hrep, htot', hpl, himm'⟩ := placedPf_of_slotRep (s := sC)
    (pf := fun k => .slot (R.addr k).toNat) hsr fun r k hk => by
      obtain ⟨jj, hl, hv⟩ := hA.slot k (hout r k hk).1
      show (Scc.Sem.X64.privLoad sC (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      show ((mC.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
      rw [hl, Option.map_some, hv]; rfl
  have hsp : SlotPlacedI Λ lbl sC c' A1 e := by
    refine ⟨envm, hrep, htot', fun y k wp hem qq hq => ?_, himm'⟩
    obtain ⟨r, k', hk', rfl⟩ := hpl y k wp hem qq hq
    exact ⟨_, rfl, r, k', hk', rfl⟩
  have h1 : FramesPlacedInI Λ lbl sC [⟨x, e, c.env, [], d.retTy⟩] A1 :=
    Spike.Lib.X64ConsumerS.FramesPlacedInI.push hsp (Spike.Lib.X64ConsumerS.FramesPlacedInI.nil A1) rfl rfl rfl rfl
  have h1' := h1.of_cKept (s' := s) (by exact hk)
    fun a ⟨r, k, hk', ha⟩ => ⟨k, (hout r k hk').1, (hout r k hk').2, ha⟩
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1'.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

/-- **The caller's frame's environment is small** under the callee's frame
condition at a call of an `Accepted2` body (`CalleeF2`'s `EnvQ`). -/
theorem envSmall_calleeF2 {fr : Scc.Emit.X64.Frame} {R : Region} {F : MachineData → Prop} {D : Int}
    {fp ra : BitVec 64} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop} (hCF : CalleeF2 p lbl lsize fr R F D fp ra i T q frm F') :
    ∀ m, F' m → EnvSmall frm.env := by
  intro m hm
  obtain ⟨-, -, mC, σC, c, t, sv, -, -, hct, -, -, ⟨lits, cs, bufs, hq⟩, -⟩ := hCF m hm
  obtain ⟨x, g, a, e, d, ty, ws, -, -, -, -, rfl⟩ := hct
  exact hq.2.1

end Frames

section CallF

variable {p : Prog} {tbl : List Scc.Cert.NeedX64.Row} {Λ : Scc.Sem.Layout} {lbl : Lbl}
  {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa} {rS : Scc.Sem.Range}

/-- **A call of an `Accepted2` body keeps the context, from the callee's
frame condition** (`CtxB.callF` at `CalleeF2`): the frames placed and
small from `framesPlaced_calleeF2`, `envSmall_calleeF2`. -/
theorem CtxB.callF2 {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {tp : UInt64}
    (hc : CtxB p tbl Λ lbl ms rS j R F fs tp) {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h16 : fr.size % 16 = 0)
    (hown : R.lo ≤ -((fr.size : Int) + 8 + 40)) {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) fr.size (-R.lo - fr.size - 16)) F')
    (hCF : CalleeF2 p lbl lsize fr (rbR R) F (-R.lo - fr.size - 16) fp ra Λ.imms T q frm F')
    {j' : Nat}
    (hroom : ∀ d, p[j']? = some d → NeedRoomX tbl (Scc.Lower.Names.user d.name) 40 (R.lo + fr.size + 16))
    (hlim : ∀ d, p[j']? = some d →
      LimRoomX tbl (Scc.Lower.Names.user d.name) ((ms []).G ⟨limA tp, 8⟩) (R.base.toNat - fr.size - 16)) :
    CtxB p tbl Λ lbl ms rS j' (calleeR (rbR R) fr.size (-R.lo - fr.size - 16)) F' (frm :: fs) tp := by
  have hhi := hc.hhi
  refine hc.call h16 hown hF' (fun m hm => ⟨(hCF m hm).1, (hCF m hm).2.1⟩) hroom hlim
    (framesPlaced_calleeF2 hf hCF (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by omega) hc.hFP) (envSmall_calleeF2 hCF)

end CallF

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.framesPlaced_calleeF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.framesPlaced_calleeF2

/-- info: 'Spike.Lib.LowerX64.CtxB.callF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CtxB.callF2
