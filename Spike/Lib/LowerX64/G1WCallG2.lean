/-
**A plain call's blocks inside `W2` at a base context** (x86-64; the twin
of `Spike/Lib/LowerA64/G1WCallG2.lean`): `wCallG2 : WCallG2`
(`Spike/Lib/LowerX64/G1CallG2.lean`), the premises `hWB`, `hWR`, `hWBl`,
`hWC` of `CallC2FW` at the `j`th compiled block's code facts under a base
context with its records, from the producers at `W2`
(`Spike/Lib/LowerX64/G1CallW2.lean`).

The base context gives the region's facts, its frame condition's stack
and frames, and `FrOk2` at its ghosts (`CxCore2`); the frame, the saved
`%rbp` and the return address lie inside the region by the block's room
(`Room2OwnStmt`). A callee `g` of the block's lowering context called on
its walk is an earlier compiled block (`hord_ofAccepted2`), whose code
facts place its prologue with its frame's function and the prologue's
phase facts (`fnCode2OfPMe_spec`, `ProOK`).

- `callee_fnCode2G`: the callee's code facts;
- `wCallG2`: the statement.
-/
import Spike.Lib.LowerX64.G1CallG2
import Spike.Lib.LowerX64.G1CallW2
import Spike.Lib.LowerX64.HordC2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1WCallG2

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A callee's code facts** at a plain call of the `j`th compiled block:
a callee `g` of the block's lowering context called at a point of its walk
is an earlier compiled block `dg` named `g` (`hord_ofAccepted2`), its code
facts at the theorem's immediates with its frame's function `g`'s and its
prologue's phase facts (`ProOK`). -/
theorem callee_fnCode2G (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) :
    ∀ (g : String), Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) →
      ∃ (dg' : Decl) (RaOk : BitVec 64 → Prop) (Cd' : BitVec 64 → Int64 → List (Directive × Nat) → Prop)
        (i' : Expr → String → Nat → Option Nat) (T' : Expr → Prop)
        (c' : FnCode2 (LY0).exe OP (LY0).endPc RaOk Cd' i' T' dg'),
        dg'.name = g ∧ c'.fr.fn = Scc.Lower.Names.user dg'.name ∧
        ProPh (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab c'.fn
          (Scc.Emit.X64.labelOf c'.fr.fn "chk") (Int64.ofInt c'.fr.size) (proL c'.fr)
          c'.zl c'.zf c'.z1 c'.z2 c'.zs c'.ps := by
  rintro g ⟨hxe, dd, hfd, -⟩ ⟨x, a, e, hT⟩
  have hfd' : p.find? (·.name == g) = some dd := by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).1] at hfd; exact hfd
  have hext : ∀ (j : Nat) d (hd : (compiled2 p)[j]? = some d),
      (FC j d hd).lcx.externs = Scc.Frontend.externs p := fun j d hd => by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]
  obtain ⟨j', -, hd'⟩ := hord_ofAccepted2 hp (T := fun j => TailAt2 p j) (fun j d hd => FC j d hd) hext j d hd
    g dd ⟨x, [], a, [], e, hT d hd, hxe⟩ hfd'
  have hP := (fnCode2OfPMe_spec hp h Λ j' dd hd').2.2
  exact ⟨dd, _, _, _, _, FC j' dd hd', by simpa using List.find?_some hfd', hP.1, hP.2.2.1⟩

/-- **A plain call's blocks inside `W2` at a base context** (`WCallG2`):
`callW2_hWB`, `callW2_hWR`, `callW2_hWBl`, `callW2_hWC` at the instance's
`InstOk`, the base context's facts (`CxCore2`, in the rebased region), the
frame, the saved `%rbp` and the return address inside the region by the
block's room (`hown`), the code predicate `CdCLE` and the call predicate
inside `BlC` (`fnCode2OfPMe_spec`), the callees' code facts
(`callee_fnCode2G`). -/
theorem wCallG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp) : WCallG2 h hp := by
  intro Dt J j d hd R F fs fp ra tp G0 Ab hcx hra
  have hc := hcx.1
  have hf := (FC j d hd).hf
  have h1 := (FC j d hd).h1
  have h16 := (FC j d hd).h16
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hBl : ∀ pc zc g k, (FC j d hd).Bl ra pc zc g k →
      BlC OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (FC j d hd).fr
        (Int64.ofBitVec ra) pc zc g k := fun pc zc g k hb => by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact hb.1.1
  have hcf := callee_fnCode2G h hp hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact callW2_hWB hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 hc.hFS hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWR hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 hc.hFS hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWBl hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hFS hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F hBl hcf
  · exact callW2_hWC hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F hcf

end G1WCallG2

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.callee_fnCode2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callee_fnCode2G

/-- info: 'Spike.Lib.LowerX64.wCallG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.wCallG2
