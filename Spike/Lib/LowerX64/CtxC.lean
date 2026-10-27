/-
**The contexts of an `Accepted1` program's functions** (x86-64, H7a
calls): the facts every function's context keeps, from `scc_rt_main`'s call
of the user `main` down through the calls, for `fnSpecC_all_ofPre`
(`Spike/Lib/LowerX64/ProgCB.lean`).

- `CtxB`: at the `j`th code block, the region `R` with frame condition `F`
  at the frames `fs` and thread pointer `tp`: the region (stable, 16-aligned less the
  return address, its top the return address's cell), the code block's
  stack room and limit room at its entry (`NeedRoomX`, `LimRoomX`), the
  region off the other stacks' words, the limit word's facts (its values
  16-aligned), the suspended frames placed with small environments.
- `CtxB.call`: a call keeps them, in the callee's region below the caller's
  frame with room `D := -R.lo - size - 16`.
- `framesPlaced_calleeF`, `envSmall_calleeF`: under the callee's frame
  condition (`CalleeF` at the layout's immediates) the frames with the
  caller's pushed placed (`slotPlacedI_of_srep` at the caller's state, kept
  by the callee, `FramesPlacedInI.cons1` on the caller's frames; through
  `lookupS_filter_ne`, `lookupS_filter_eq`) and the caller's environment
  small; `CtxB.callF`: `CtxB.call` from `CalleeF`.
- `rsOf_param`, `nj_callee`: the callee's `Int` parameter has a slot, and
  the source's entry control of a call is the callee's body node there.
- `CxOkC`, `AbC`, `CxOkC.hab`: the code blocks' contexts (`CtxB`, the
  `Good1` ghosts with no hold, the aborts `AbC`) and their aborts.
-/
import Spike.Lib.LowerX64.ProgCB
import Spike.Lib.LowerX64.CalleeRoom
import Spike.Lib.LowerX64.LimRoom
import Spike.Lib.LowerX64.UserCall
import Spike.Lib.X64FramesPlacedI
import Spike.Lib.LowerShapeX64

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (CallerCells StackOff limA)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (FramesPlacedInI)

/-- **A function's context** at the `j`th code block (see the module
docstring): the region `R` (entry `%rsp` its base) and frame condition `F`
at the frames `fs`, the thread pointer `tp`, for the stack need table
`tbl`, the layout `Λ`, the memory sides `ms`, the other stacks' range
and the other stacks' range `rS`. -/
structure CtxB (p : Prog) (tbl : List Scc.Cert.NeedX64.Row) (Λ : Scc.Sem.Layout) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isa) (rS : Scc.Sem.Range) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (tp : UInt64) : Prop where
  hF : FStable R F
  hR : R.OK
  hb16 : R.base.toNat % 16 = 8
  hl8 : R.lo % 8 = 0
  hhi : R.hi = 8
  room : ∀ d, p[j]? = some d → NeedRoomX tbl (Scc.Lower.Names.user d.name) 40 R.lo
  lim : ∀ d, p[j]? = some d → LimRoomX tbl (Scc.Lower.Names.user d.name) ((ms []).G ⟨limA tp, 8⟩) R.base.toNat
  hFO : ∀ m, F m → StackOff rS R m
  limRt : (ms []).rt (limA tp).toNat
  limMp : (ms []).mp ⟨limA tp, 8⟩ false
  limUn : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none
  g16 : ∀ v, (ms []).G ⟨limA tp, 8⟩ v → (v.setWidth 64).toNat % 16 = 0
  hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A
  hes : ∀ m, F m → ∀ f ∈ fs, EnvSmall f.env

section Call

variable {p : Prog} {tbl : List Scc.Cert.NeedX64.Row} {Λ : Scc.Sem.Layout} {lbl : Lbl}
  {ms : List TermRun.Frame → MemSide isa} {rS : Scc.Sem.Range}

/-- **The rebased region's base** is the entry's less the return address. -/
theorem rbR_base {R : Region} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 0 ≤ R.hi) :
    ((rbR R).base.toNat : Int) = R.base.toNat - 8 :=
  Region.callee_base (hi' := R.hi + 8) hR (by omega) (by omega) (by omega)

/-- **The callee's region's base** below the caller's frame of `size`
bytes, its saved `%rbp` and the return address, at the room
`D := -R.lo - size - 16`. -/
theorem calleeR_base {R : Region} (hR : R.OK) (hhi : R.hi = 8) {size : Nat} (hlo : R.lo ≤ -(size : Int) - 16) :
    ((calleeR (rbR R) size (-R.lo - size - 16)).base.toNat : Int) = R.base.toNat - size - 16 := by
  have hb := rbR_base hR (by omega) (by omega)
  have hrb := rbR_ok hR (by omega) (by omega)
  have := Region.callee_base (R := rbR R) (hi' := 8) (kc := -(size : Int) - 8) (lo' := -(-R.lo - size - 16)) hrb
    (by simp only [rbR, Region.callee]; omega) (by omega) (by simp only [rbR, Region.callee]; omega)
  simp only [calleeR]
  omega

/-- **A call keeps the context**: at a call from the `j`th code block's
context, with a frame of `size` bytes (16-aligned, within the block's room,
`hown`), the callee's region below it at room `D := -R.lo - size - 16`
with a stable frame condition `F'` inside the caller's with the caller's
cells (`hCF`, `CalleeF`'s), the callee the `j'`th code block
with its rooms at its entry (`hroom`, `hlim`), its frames placed and small
(`hFP`, `hes`). -/
theorem CtxB.call {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {tp : UInt64}
    (hc : CtxB p tbl Λ lbl ms rS j R F fs tp) {size : Nat} (h16 : size % 16 = 0)
    (hown : R.lo ≤ -((size : Int) + 8 + 40)) {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) size (-R.lo - size - 16)) F')
    (hCF : ∀ m, F' m → F m ∧ CallerCells (rbR R) (-(size : Int) - 8) (-(-R.lo - size - 16)) 8 m)
    {j' : Nat} {frm : TermRun.Frame}
    (hroom : ∀ d, p[j']? = some d → NeedRoomX tbl (Scc.Lower.Names.user d.name) 40 (R.lo + size + 16))
    (hlim : ∀ d, p[j']? = some d →
      LimRoomX tbl (Scc.Lower.Names.user d.name) ((ms []).G ⟨limA tp, 8⟩) (R.base.toNat - size - 16))
    (hFP : ∀ s : State, F' s.st.1 → ∃ A, FramesPlacedInI Λ lbl s (frm :: fs) A)
    (hes : ∀ m, F' m → EnvSmall frm.env) :
    CtxB p tbl Λ lbl ms rS j' (calleeR (rbR R) size (-R.lo - size - 16)) F' (frm :: fs) tp := by
  have hR := hc.hR
  have hhi := hc.hhi
  have hl8 := hc.hl8
  have hb16 := hc.hb16
  have hrb := rbR_ok hR (by omega) (by omega)
  have hb := rbR_base hR (by omega) (by omega)
  have hcb := calleeR_base hR hhi (size := size) (by omega)
  have hrb8 : (rbR R).base.toNat % 8 = 0 := by omega
  refine ⟨hF', ?_, ?_, ?_, rfl, ?_, ?_, ?_, hc.limRt, hc.limMp, ?_, hc.g16, hFP, ?_⟩
  · exact calleeR_ok hrb (by omega) (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega)
  · omega
  · simp only [calleeR, Region.callee]
    omega
  · intro d hd
    have e : (calleeR (rbR R) size (-R.lo - size - 16)).lo = R.lo + size + 16 := by
      simp only [calleeR, Region.callee]; omega
    rw [e]
    exact hroom d hd
  · intro d hd
    have : (calleeR (rbR R) size (-R.lo - size - 16)).base.toNat = R.base.toNat - size - 16 := by omega
    rw [this]
    exact hlim d hd
  · intro m hm
    obtain ⟨hFm, hcc⟩ := hCF m hm
    exact Spike.Lib.X64.Rt.stackOff_callee hrb hrb8 (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega) (by omega)
      (by simp only [rbR, Region.callee]; omega) (by omega)
      (stackOff_rbR hR (by omega) (by omega) (hc.hFO m hFm)) hcc
  · exact fun m hm => hc.limUn m (hCF m hm).1
  · intro m hm f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hes m hm
    · exact hc.hes m (hCF m hm).1 f hf

end Call

section Frames

open Spike.Lib.X64ConsumerS (SlotPlacedI slotPlacedI_of_srep)
open Spike.Lib.Form (SEnv lookupS)
open Spike.Lib.X64.Flow (CallTo)

variable {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl}

/-- A symbolic environment less `x`'s bindings looks `y ≠ x` up alike. -/
theorem lookupS_filter_ne (sv : SEnv) {x y : String} (h : y ≠ x) :
    lookupS (sv.filter (·.1 != x)) y = lookupS sv y := by
  induction sv with
  | nil => rfl
  | cons b sv ih =>
    unfold lookupS at ih ⊢
    by_cases hb : b.1 = x
    · have hby : (b.1 == y) = false := by
        rw [beq_eq_false_iff_ne, hb]; exact fun h' => h h'.symm
      have hb' : (b.1 != x) = false := by simp [hb]
      rw [List.filter_cons_of_neg (by simp [hb']), List.find?_cons]
      simp only [hby]
      exact ih
    · have hb' : (b.1 != x) = true := by simpa using hb
      rw [List.filter_cons_of_pos (p := fun x_1 : String × Ty × List Spike.Lib.Form.WordPl => x_1.fst != x) hb',
        List.find?_cons, List.find?_cons]
      split <;> simp_all

/-- A symbolic environment less `x`'s bindings has none for `x`. -/
theorem lookupS_filter_eq (sv : SEnv) (x : String) : lookupS (sv.filter (·.1 != x)) x = none := by
  unfold lookupS
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro b hb
  have := (List.mem_filter.mp hb).2
  simp only [bne_iff_ne, ne_eq] at this
  simpa using this

/-- **Frames placed, one on top of more**: a frame placed by itself and
frames below it placed, at one state and slots, place them all. -/
theorem FramesPlacedInI.cons1 {s : State} {f : TermRun.Frame} {fs : List TermRun.Frame} {A : Nat → Prop}
    (h1 : FramesPlacedInI Λ lbl s [f] A) (h2 : FramesPlacedInI Λ lbl s fs A) :
    FramesPlacedInI Λ lbl s (f :: fs) A := by
  obtain ⟨e1, hrep1, htot1, hin1, himm1⟩ := h1
  obtain ⟨e2, hrep2, htot2, hin2, himm2⟩ := h2
  refine ⟨fun d => match d with | 0 => e1 0 | d + 1 => e2 d, ?_, ?_, ?_, ?_⟩
  · intro d f' hfd y ty ws hy k wd wp hwd hwp
    rcases d with _ | d
    · exact hrep1 0 f' (by simpa using hfd) y ty ws hy k wd wp hwd hwp
    · exact hrep2 d f' (by simpa using hfd) y ty ws hy k wd wp hwd hwp
  · intro d f' hfd y hy ty ws hl k hk
    rcases d with _ | d
    · exact htot1 0 f' (by simpa using hfd) y hy ty ws hl k hk
    · exact htot2 d f' (by simpa using hfd) y hy ty ws hl k hk
  · intro d y k wp hwp
    rcases d with _ | d
    · exact hin1 0 y k wp hwp
    · exact hin2 d y k wp hwp
  · intro d f' y k n hfd hwp
    rcases d with _ | d
    · exact himm1 0 f' y k n (by simpa using hfd) hwp
    · exact himm2 d f' y k n (by simpa using hfd) hwp

/-- **The frames at the callee's entry placed** under its frame condition
(`CalleeF` at the layout's immediates): the caller's frame `frm`, from the
lowering's node invariant at the call (`slotPlacedI_of_srep` at the
caller's state, its slots among its frame's cells, kept by the callee,
`CalleeF.framesKept`), on the caller's frames `fs` placed under the
caller's frame condition. -/
theorem framesPlaced_calleeF {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF p lbl fr R F D fp ra Λ.imms T q frm F')
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A) :
    ∀ s : State, F' s.st.1 → ∃ A, FramesPlacedInI Λ lbl s (frm :: fs) A := by
  intro s hm
  obtain ⟨A2, h2⟩ := hFP s (hCF.inF _ hm)
  obtain ⟨mC, σC, c, t, sv, hA, hk, hct, -, hj, hen, -, htot, himm⟩ := hCF.callerI hm
  obtain ⟨x, g, a, e, d, ty, ws, -, -, -, -, rfl⟩ := id hct
  have hout : ∀ r k, rsOf fr r = some k →
      R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-D) 8).Off (k - (-(fr.size : Int) - 8)) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk
    exact frame_out hlo hhi hD0 hk2 (by omega) (by omega)
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf fr r = some k ∧ a = (R.addr k).toNat
  let sC : State := { s with st := (mC, s.st.2) }
  have hsp : SlotPlacedI Λ lbl sC { c with term := .let_ x (.atom .unit) e } A1 e := by
    refine slotPlacedI_of_srep (rs := rsOf fr) (senv := sv.filter (·.1 != x)) (sl := σC.slot) (addr := R.addr)
      ?_ hen ?_ ?_ (fun r k hk => ⟨r, k, hk, rfl⟩) ?_
    · intro y ty' pls hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact hj.2.2 y ty' pls hl
    · intro y hy
      have hy : y ∈ Scc.Sem.exprFv e ∧ y ≠ x := by
        simpa [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars] using hy
      rw [lookupS_filter_ne _ hy.2]
      exact htot y hy.1 hy.2
    · intro r k hk
      obtain ⟨jj, hl, hv⟩ := hA.slot k (hout r k hk).1
      show (mC.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64) = _
      rw [hl, Option.map_some, hv]
    · intro y k v hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact himm y k v hy hl
  have h1 : FramesPlacedInI Λ lbl sC [⟨x, e, c.env, [], d.retTy⟩] A1 :=
    Spike.Lib.X64ConsumerS.FramesPlacedInI.push hsp (Spike.Lib.X64ConsumerS.FramesPlacedInI.nil A1) rfl rfl rfl rfl
  have h1' := CalleeF.framesKept (fr := fr) (D := D) (sC := sC) (s := s) rfl hk h1
    fun a ⟨r, k, hk', ha⟩ => ⟨k, (hout r k hk').1, (hout r k hk').2, ha⟩
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1'.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

/-- **The caller's frame's environment is small** under the callee's frame
condition (`CalleeF`'s numeric environment). -/
theorem envSmall_calleeF {fr : Scc.Emit.X64.Frame} {R : Region} {F : MachineData → Prop} {D : Int}
    {fp ra : BitVec 64} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop} (hCF : CalleeF p lbl fr R F D fp ra i T q frm F') :
    ∀ m, F' m → EnvSmall frm.env := by
  intro m hm
  obtain ⟨mC, σC, c, t, sv, -, -, hct, -, -, hen, -⟩ := hCF.callerI hm
  obtain ⟨x, g, a, e, d, ty, ws, -, -, -, -, rfl⟩ := hct
  exact AbortSrc.envSmall_of_envNum hen

end Frames

section CallF

variable {p : Prog} {tbl : List Scc.Cert.NeedX64.Row} {Λ : Scc.Sem.Layout} {lbl : Lbl}
  {ms : List TermRun.Frame → MemSide isa} {rS : Scc.Sem.Range}

/-- **A call keeps the context, from the callee's frame condition**
(`CtxB.call` with `CalleeF` at the layout's immediates): the caller's
frame `fr` within the block's room (`hown`), the callee's frame condition
`F'` stable, the callee the `j'`th code block with its rooms at
its entry (`hroom`, `hlim`); the frames placed and small from `CalleeF`
(`framesPlaced_calleeF`, `envSmall_calleeF`). -/
theorem CtxB.callF {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {tp : UInt64}
    (hc : CtxB p tbl Λ lbl ms rS j R F fs tp) {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h16 : fr.size % 16 = 0)
    (hown : R.lo ≤ -((fr.size : Int) + 8 + 40)) {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) fr.size (-R.lo - fr.size - 16)) F')
    (hCF : CalleeF p lbl fr (rbR R) F (-R.lo - fr.size - 16) fp ra Λ.imms T q frm F')
    {j' : Nat}
    (hroom : ∀ d, p[j']? = some d → NeedRoomX tbl (Scc.Lower.Names.user d.name) 40 (R.lo + fr.size + 16))
    (hlim : ∀ d, p[j']? = some d →
      LimRoomX tbl (Scc.Lower.Names.user d.name) ((ms []).G ⟨limA tp, 8⟩) (R.base.toNat - fr.size - 16)) :
    CtxB p tbl Λ lbl ms rS j' (calleeR (rbR R) fr.size (-R.lo - fr.size - 16)) F' (frm :: fs) tp := by
  have hhi := hc.hhi
  refine hc.call h16 hown hF' (fun m hm => ⟨hCF.inF m hm, hCF.callerCells m hm⟩) hroom hlim
    (framesPlaced_calleeF hf hCF (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by omega) hc.hFP) (envSmall_calleeF hCF)

end CallF

section Entry

open Spike.Lib.Form (lookupS)
open Spike.Lib.X64.Flow (CallTo)
open Scc.Lower.Inv (env1 params1R func1 Res1)
open Spike.Lib.LowerNode (NJ ofEnv)

/-- **An `Int` parameter's register has a slot** in an `Accepted1` code
block's frame. -/
theorem rsOf_param (ir : Scc.IR.Program) (name : String) {d : Decl} (hint : d.argTy = .int) (r : Res1) :
    ∃ k, rsOf (frOf ir (func1 name (params1R d) r)) s!"{d.arg}.{0}" = some k := by
  obtain ⟨k, hk⟩ := Spike.Lib.LowerShape.slotOff_param (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length)
    (func1 name (params1R d) r) (r := s!"{d.arg}.{0}") (by simp [func1, params1R, hint])
  refine ⟨-(8 * (k + 1)), ?_⟩
  unfold rsOf
  rw [show (frOf ir (func1 name (params1R d) r)).slotOff s!"{d.arg}.{0}" {} =
    (Scc.Emit.X64.frameOf (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length)
      (func1 name (params1R d) r)).slotOff s!"{d.arg}.{0}" {} from rfl, hk {}]

/-- **The callee's body node at its entry**: the source's entry control
`q.cE` of a call to `d` (an `Int` parameter, `hint`) binding the argument
(`ArgV`), the parameter's register's cell `k` holding the argument's value
`q.v`, is the body's node of `env1 d` (no local step). -/
theorem nj_callee {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {d : Decl} (hint : d.argTy = .int)
    {q : CallG} (harg : ArgV lbl q) {ws : List TermRun.Word} (hcE : q.cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩)
    {rs : Scc.IR.Reg → Option Int} {k : Int} (hk : rs s!"{d.arg}.{0}" = some k) {sl : Int → BitVec 64}
    (hsl : sl k = q.v) : NJ p lbl rs d.body (ofEnv (env1 d)) sl q.cE := by
  have hen := harg.envNum
  obtain ⟨x, t, w, he, hv, -⟩ := harg
  rw [hcE] at he
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine NJ.of_nodeJ ⟨by rw [hcE], by rw [hcE], ?_⟩ hen
  intro y ty pls hl
  simp only [env1, params1R, hint, ofEnv, lookupS, beq_self_eq_true, ite_true, List.map, List.find?] at hl
  by_cases hy : d.arg = y
  · subst hy
    simp only [beq_self_eq_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨[w], by rw [hcE]; simp [TermRun.lookupE, hint], ⟨(sl k).toNat, ?_, ?_⟩, trivial⟩
    · show (rs _).map (fun k => (sl k).toNat) = _
      rw [show rs s!"{d.arg}.{0}" = some k from hk]
      rfl
    · rw [hsl]; exact hv
  · have hy' : (d.arg == y) = false := by simpa using hy
    simp [hy'] at hl

end Entry

section Ok

variable {p : Prog} {tbl : List Scc.Cert.NeedX64.Row} {Λ : Scc.Sem.Layout} {lbl : Lbl}
  {ms : List TermRun.Frame → MemSide isa} {rS : Scc.Sem.Range}

/-- **The contexts of the `j`th code block** (`fnSpecC_all_ofPre`'s
`CxOk j`): `CtxB` at the region, frame condition, frames and thread
pointer, the ghosts the `Good1` controls with no hold at the frames, the
aborts `Ab`. -/
def CxOkC (p : Prog) (tbl : List Scc.Cert.NeedX64.Row) (Λ : Scc.Sem.Layout) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isa) (rS : Scc.Sem.Range) (Ab : FragS isa) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (_fp _ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab' : FragS isa) : Prop :=
  CtxB p tbl Λ lbl ms rS j R F fs tp ∧ G0 = (fun c => Good1 p (c, fs) ∧ c.hold = none) ∧ Ab' = Ab

/-- **The aborts of the code blocks at their contexts**: the overflow abort
label of the `j`th code block `hcode j d hd` at a context (`CtxB`, a return
address with `RaOk`, a `Good1` ghost with no hold), in its rebased region. -/
def AbC (p : Prog) (tbl : List Scc.Cert.NeedX64.Row) (Λ : Scc.Sem.Layout) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isa) (rS : Scc.Sem.Range) {exe : _root_.Executable}
    {cells : List (Directive × Nat)} {endPc : Int64} {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop} {i : Expr → String → Nat → Option Nat}
    {T : Nat → Expr → Prop} (hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe cells endPc RaOk Cd i (T j) d) :
    FragS isa :=
  fun s c fs => ∃ (j : Nat) (d : Decl) (hd : p[j]? = some d) (R : Region) (F : MachineData → Prop) (tp : UInt64)
    (fp ra : BitVec 64) (c0 : Ctl), CtxB p tbl Λ lbl ms rS j R F fs tp ∧ RaOk ra ∧ Good1 p (c0, fs) ∧
      c0.hold = none ∧
      At exe endPc (rbR R) F (abortN i (T j) p lbl (hcode j d hd).fr (_root_.Executable.labels exe).label fp ra c0) s c

/-- **A context's aborts are among `AbC`'s** (`CalleePre`'s `hab`). -/
theorem CxOkC.hab {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe cells endPc RaOk Cd i (T j) d}
    {j : Nat} {d : Decl} (hd : p[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (h : CxOkC p tbl Λ lbl ms rS (AbC p tbl Λ lbl ms rS hcode) j R F fs fp ra tp G0 Ab) (hra : RaOk ra) :
    ∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F (abortN i (T j) p lbl (hcode j d hd).fr (_root_.Executable.labels exe).label fp ra c0)
        s c' → Ab s c' fs := by
  obtain ⟨hc, rfl, rfl⟩ := h
  intro c0 hg s c' hA
  exact ⟨j, d, hd, R, F, tp, fp, ra, c0, hc, hra, hg.1, hg.2, hA⟩

end Ok

end Spike.Lib.LowerX64
