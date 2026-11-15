/-
**A plain call's callee-side facts** (x86-64; the twin of
`Spike/Lib/LowerA64/G1CalleeFacts.lean`): the facts a callee's context
premises (`CalleePre2`) ask for at a plain call of an `Accepted2` program,
from the caller's `call` (`BlC2L`), the placement check and the stack need
table.

- `raOk_of_blC2L`: the return address `pc + zc` of a `call` at `pc` is in
  the phase of the caller's return address;
- `posOff_ra_of_blC2L`: the return address is a position off the write
  abort (the return label's);
- `posOff_proL_FC`: a compiled block's overflow target is a position off
  the write abort;
- `LimRoomX.frame`, `limRoom_sub_frame`: a limit room whose row covers the
  frame and the saved `%rbp` bounds every limit value by the new frame's
  `%rsp`;
- `calleeJSO`, `hcal_ofSO`: `hcal_of` at the entry invariant with `%rsp`
  at the callee's region's base (`SORel` at offset `0`), which every entry
  state has.
-/
import Spike.Lib.LowerX64.G1CallCx
import Spike.Lib.LowerX64.AllocRa
import Spike.Lib.LowerX64.FnCodeLB
import Spike.Lib.LowerX64.ProgC2
import Spike.Lib.LowerX64.UserLabs
import Spike.Lib.LowerX64.StkOf

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.LowerNode (compiled2)

/-! ## The return address -/

/-- **A `call`'s return address is in the caller's return address's
phase**: the return address `ra'` is `pc + zc` for the `call` at `pc` of
`zc` bytes, whose phase is the caller's `ra`'s (`BlC`). -/
theorem raOk_of_blC2L {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2L cells okPc ph lab fr ra pc zc g k) {A : Nat} (hra : ph ra.toBitVec.toNat = A) {ra' : BitVec 64}
    (hq : ra' = (pc + Int64.ofNat zc).toBitVec) :
    ph (Int64.ofBitVec ra').toBitVec.toNat = A := by
  subst hq
  obtain ⟨⟨⟨-, -, -, -, -, -, -, hph⟩, -⟩, -⟩ := h
  rw [← hra, ← hph]
  rfl

/-- **A `call`'s return address is a position off the write abort**: the
return label `.L<fn>.x<k>` (in the code, `BlC2`, and none of the
runtime's, `ret_not_abLabs`) at its first cell (`blC2_ret`). -/
theorem posOff_ra_of_blC2L {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {okPc : Nat → Bool} {ph : Nat → Nat}
    {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2L cells okPc ph (_root_.Executable.labels exe).label fr ra pc zc g k) {ra' : BitVec 64}
    (hq : ra' = (pc + Int64.ofNat zc).toBitVec) :
    PosOff cells (_root_.Executable.labels exe).label (Int64.ofBitVec ra') := by
  subst hq
  have hr := blC2_ret hp h.1
  exact ⟨s!".L{fr.fn}.x{k}", 0, h.1.2.2, ret_not_abLabs _ _, by rw [← hr]; rfl⟩

/-! ## The overflow target -/

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

/-- **A compiled block's overflow target is a position off the write
abort** (`proW_abStC`'s `hL`): the block's function passes A12
(`fnCode1_of_placeOKAt`, the lowering's functions checking the stack), its
frame the placement check's (`fnCode2OfPMe_spec2`), its labels a user
function's (`labelOf_user_not_abLabs`). -/
theorem posOff_proL_FC (Λm : Scc.Sem.Layout) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d)
    (lab : Label → Int64) :
    PosOff (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) lab
      (lab (proL (fnCode2OfPMe hp h Λm j d hd).fr)) := by
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λm j d hd
  obtain ⟨n, hst⟩ := mem_starts (Scc.Lower.X64.lowerAll cfg p).low.ir 0 hmem
  have hok := Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok
    (Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)) hst rfl
  rw [hcx]
  exact posOff_proL_of_fnOk1 hok (labelOf_user_not_abLabs _ _) lab

end Place

/-! ## The limit room -/

/-- **A limit room whose row covers the frame `fr` and the saved `%rbp`**
(every room of the row at least `fr + 8` below, the shape of
`Room2OwnStmt`) bounds every limit value by `sp - fr`. -/
theorem LimRoomX.frame {tbl : List Scc.Cert.NeedX64.Row} {name : String} {G : Kraken.Promising.Val → Prop}
    {sp fr : Nat} (hL : LimRoomX tbl name G sp)
    (hown : ∀ s lo, NeedRoomX tbl name s lo → lo ≤ -((fr : Int) + 8 + s)) :
    ∀ v, G v → (v.setWidth 64).toNat + fr ≤ sp := by
  obtain ⟨a, f, n, hr, hv⟩ := hL
  have := hown 0 (-(n : Int)) ⟨a, f, n, hr, by omega⟩
  intro v hv'
  have := hv v hv'
  omega

/-- **The new frame's `%rsp` bounds the limit values** (`LimOk2Stmt`'s
premise): `%rsp` of value at least `x + 8 + fr`, the frame `fr` a small
number, leaves `x` at most `%rsp - 8 - fr`. -/
theorem limRoom_sub_frame {spv : BitVec 64} {fr : Nat} (h1 : fr ≤ 2 ^ 31) {x : Nat}
    (hx : x + 8 + fr ≤ spv.toNat) :
    x ≤ (spv - 8#64 - (Int64.ofInt (fr : Int)).toBitVec).toNat := by
  have hf : (Int64.ofInt (fr : Int)).toBitVec.toNat = fr := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    have : ((fr : Int) % (2 ^ 64 : Nat)) = fr := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; rfl
  have := spv.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hf, BitVec.toNat_ofNat]
  omega

/-! ## The callee's segment at an entry with `%rsp` placed -/

section ProgC2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **The callee's entry invariant with `%rsp` at the region's base**:
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
theorem hcal_ofSO {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {dg : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T dg} {g : String} (hg : dg.name = g) (hint : dg.retTy = .int)
    {q : CallG} {frm : TermRun.Frame} (hty : frm.ty = dg.retTy) {R' : Region} {F' : MachineData → Prop}
    {fs : List TermRun.Frame} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R' F' (frm :: fs) q.fp q.ra tp G0 Ab
      (calleeJSO R' F' (_root_.Executable.labels exe).label g tp q) q.cE)
    (hs : FnSpecC2 W K p lbl lsize ms CxOk c) :
    SegWS W K p lbl ms ((At exe endPc R' F' (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
      (ExitC2B p lbl exe endPc (rbR R') F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab) := by
  have hseg := h.segB hs (List.cons_ne_nil _ _) hty.symm (hty.trans hint)
  refine hseg.mono_pre ?_
  rintro s c' fs' ⟨⟨he, hn, hdc, hpc, σ, hA, hF, hJ⟩, rfl⟩
  refine ⟨⟨he, hn, hdc, ?_, σ, hA, hF, hJ, hA.so, _, hF⟩, rfl⟩
  rw [hpc]
  show (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) = _
  rw [c.hfn, hg]

end ProgC2

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.raOk_of_blC2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.raOk_of_blC2L

/-- info: 'Spike.Lib.LowerX64.posOff_ra_of_blC2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_ra_of_blC2L

/-- info: 'Spike.Lib.LowerX64.posOff_proL_FC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_proL_FC

/-- info: 'Spike.Lib.LowerX64.LimRoomX.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.LimRoomX.frame

/-- info: 'Spike.Lib.LowerX64.limRoom_sub_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limRoom_sub_frame

/-- info: 'Spike.Lib.LowerX64.hcal_ofSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hcal_ofSO
