/-
**A plain call's callee-side facts** (AArch64): the facts a callee's
context premises (`CalleePre2`) ask for at a plain call of an `Accepted2`
program, from the caller's `bl` (`BlC2L`), the placement check and the
stack need table.

- `raOk_of_blC2L`: the return address `pc + 4` of a `bl` at `pc` is in the
  phase of the caller's return address;
- `posOff_ra_of_blC2L`: the return address is a position off the write
  abort (the return label's);
- `posOff_proL_FC`: a compiled block's overflow target is a position off
  the write abort;
- `LimRoomA.frame`, `limRoom_sub_frame`: a limit room whose row covers the
  frame bounds every limit value by the new frame's `sp`;
- `hcal_ofSO`: `hcal_of` at the entry invariant with `sp` at the callee's
  region's base (`SORel` at offset `0`), which every entry state has.
-/
import Spike.Lib.LowerA64.G1CallCx
import Spike.Lib.LowerA64.StkOfA
import Spike.Lib.LowerA64.AllocRa
import Spike.Lib.LowerA64.FnCodeLB
import Spike.Lib.LowerA64.ProgC2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (Lays)
open Spike.Lib.LowerNode (compiled2)

/-! ## The return address -/

/-- **A `bl`'s return address is in the caller's return address's
phase**: the return address `ra'` is `pc + 4` for the `bl` at `pc`, whose
phase is the caller's `ra`'s (`BlC`). -/
theorem raOk_of_blC2L {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {cx : FnCtx} {ra pc : Int64} {g : Label} {k : Nat} (h : BlC2L prog okPc ph lab cx ra pc g k) {A : Nat}
    (hra : ph ra.toBitVec.toNat = A) {ra' : BitVec 64} (hq : ra' = (pc + 4).toBitVec) :
    ph (Int64.ofBitVec ra').toBitVec.toNat = A := by
  subst hq
  obtain ⟨⟨⟨-, -, -, -, -, -, hph⟩, -⟩, -⟩ := h
  rw [← hra, ← hph]
  rfl

/-- **A `bl`'s return address is a position off the write abort**: the
return label `sp{k}` (in the code, `BlC2`, and a local label of a function
none of the runtime's, `local_not_abLabs`) at its first instruction
(`blC2_ret`). -/
theorem posOff_ra_of_blC2L {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) {okPc : Nat → Bool} {ph : Nat → Nat}
    {cx : FnCtx} {ra pc : Int64} {g : Label} {k : Nat}
    (h : BlC2L prog okPc ph (_root_.Executable.labels exe).label cx ra pc g k)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) {ra' : BitVec 64} (hq : ra' = (pc + 4).toBitVec) :
    PosOff prog (_root_.Executable.labels exe).label (Int64.ofBitVec ra') := by
  subst hq
  have hr := blC2_ret hp h.1
  exact ⟨cx.local s!"sp{k}", 0, h.1.2.2, local_not_abLabs hfi _, by rw [← hr]; rfl⟩

/-! ## The overflow target -/

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

/-- **A compiled block's overflow target is a position off the write
abort** (`proW_abStC`'s `hL`): the block's function passes A12
(`fnCode1_of_placeOKAt`, the lowering's functions checking the stack),
its context the placement check's (`fnCode2OfPMe_spec2`), its index none of
the runtime's (`ProOK`). -/
theorem posOff_proL_FC (Λm : Scc.Sem.Layout) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d)
    (lab : Label → Int64) :
    PosOff (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) lab
      (lab (proL (fnCode2OfPMe hp h Λm j d hd).cx)) := by
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λm j d hd
  have hfi := (fnCode2OfPMe_spec hp h Λm j d hd).2.2.1
  have h12 := Scc.Cert.PlaceOK.A64.fnCode1_of_placeOKAt h (place_ir_ofEmitted _)
  have hok := Scc.Cert.Code1A64.fnOk1_of_fnCode1Ok h12 hmem rfl
  rw [hcx] at hfi ⊢
  exact posOff_proL_of_fnOk1 hok (local_not_abLabs hfi _) lab

end Place

/-! ## The limit room -/

/-- **A limit room whose row covers the frame `fr`** (every room of the
row at least `fr` below, the shape of `Room2OwnStmt`) bounds every limit
value by `sp - fr`. -/
theorem LimRoomA.frame {tbl : List Scc.Cert.NeedA64.Row} {name : String} {G : Kraken.Promising.Val → Prop}
    {sp fr : Nat} (hL : LimRoomA tbl name G sp)
    (hown : ∀ s lo, NeedRoomA tbl name s lo → lo ≤ -((fr : Int) + s)) :
    ∀ v, G v → (v.setWidth 64).toNat + fr ≤ sp := by
  obtain ⟨a, f, n, hr, hv⟩ := hL
  have := hown 0 (-(n : Int)) ⟨a, f, n, hr, by omega⟩
  intro v hv'
  have := hv v hv'
  omega

/-- **The new frame's `sp` bounds the limit values** (`LimOk2Stmt`'s
premise): `sp` of value at least `x + fr`, the frame `fr` a small number,
leaves `x` at most `sp - fr`. -/
theorem limRoom_sub_frame {spv : BitVec 64} {fr : Nat} (h1 : fr ≤ 4095) {x : Nat} (hx : x + fr ≤ spv.toNat) :
    x ≤ (spv - (Int64.ofInt (fr : Int)).toBitVec).toNat := by
  have hf : (Int64.ofInt (fr : Int)).toBitVec.toNat = fr := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    have : ((fr : Int) % (2 ^ 64 : Nat)) = fr := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; rfl
  rw [BitVec.toNat_sub, hf]
  have := spv.isLt
  rw [show 2 ^ 64 - fr + spv.toNat = (spv.toNat - fr) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The callee's segment at an entry with `sp` placed -/

section ProgC2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The callee's entry invariant with `sp` at the region's base**:
`calleeN`'s, the registers agreeing with offset `0` in the callee's region
`R'` (every state of `calleeN`'s fragment has it, `Abs.so`), and the frame
condition `F'` inhabited (by the state's machine data). -/
def calleeJSO (R' : Region) (F' : MachineData → Prop) (lab : Label → Int64) (g : String) (tp : UInt64)
    (q : CallG) : AS → Ctl → Prop :=
  fun σ c => (calleeN lab g tp q).J σ c ∧ SORel R' ⟨0, []⟩ σ.regs ∧ ∃ m, F' m

omit [Kraken.Executable.ValidLayout exe] in
/-- **A plain call's callee segment** (`hcal_of`) from the callee's context
premises at the entry invariant `calleeJSO`: `calleeN`'s fragment's states
are at offset `0` (`Abs.so`) in `F'`, so they are `calleeJSO`'s. -/
theorem hcal_ofSO {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {dg : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode2 exe prog endPc RaOk Cd i T dg} {g : String} (hg : dg.name = g) (hint : dg.retTy = .int)
    {q : CallG} {frm : TermRun.Frame} (hty : frm.ty = dg.retTy) {R' : Region} {F' : MachineData → Prop}
    {fs : List TermRun.Frame} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R' F' (frm :: fs) q.fp q.ra tp G0 Ab
      (calleeJSO R' F' (_root_.Executable.labels exe).label g tp q) q.cE)
    (hs : FnSpecC2 W K p lbl lsize ms CxOk c) :
    SegWS W K p lbl ms ((At exe endPc R' F' (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
      (ExitC2B p lbl exe endPc R' F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab) := by
  have hseg := h.segB hs (List.cons_ne_nil _ _) hty.symm (hty.trans hint)
  refine hseg.mono_pre ?_
  rintro s c' fs' ⟨⟨he, hn, hdc, hpc, σ, hA, hF, hJ⟩, rfl⟩
  refine ⟨⟨he, hn, hdc, ?_, σ, hA, hF, hJ, hA.so, _, hF⟩, rfl⟩
  rw [hpc]
  show (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) = _
  rw [c.hfn, hg]

end ProgC2

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.raOk_of_blC2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.raOk_of_blC2L

/-- info: 'Spike.Lib.LowerA64.posOff_ra_of_blC2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.posOff_ra_of_blC2L

/-- info: 'Spike.Lib.LowerA64.posOff_proL_FC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.posOff_proL_FC

/-- info: 'Spike.Lib.LowerA64.LimRoomA.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.LimRoomA.frame

/-- info: 'Spike.Lib.LowerA64.limRoom_sub_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limRoom_sub_frame

/-- info: 'Spike.Lib.LowerA64.hcal_ofSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hcal_ofSO
