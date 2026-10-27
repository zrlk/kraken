/-
**The stack limit's facts at any level** (x86-64, `LimOk` at depth; the
twin of `Spike/Lib/LowerA64/LimLvl2.lean`): the first TCB's limit word's
facts (`LimOk`) under the rows' memory side `msOfAX` at any placement
reachable by allocations from the empty one, at any frames and any abort
phase, at a placed output. The runtime's words lie in `.data`/`pinned`, off
the arena (`rtWords_offArena`), and every label a reachable placement
places lies inside the arena (`LblArena.reach`), so no placed label covers
a runtime word (`RtFree`) at any level.

- `rtFree_ofArena`: `RtFree` from every label inside an arena the runtime's
  words are off;
- `limOk_toAXF`: `limOk_toAX` at any frames and any owned words;
- `rtFree_lvl_ofPlaceOK`: `RtFree` at every placement reachable from the
  empty one in the output's arena `arOf`;
- `limOk_lvl_ofPlaceOK`: the first TCB's limit word's facts under
  `msOfAX` at such a placement, at any frames, for any bound past the
  limit (`limOk_ofPlaceOK` at depth);
- `limOk_callee_lvl`: a callee's prologue limit facts at such a placement
  (at the first thread's `%fs` base, the stack-depth bound `StkRoomX`).
-/
import Spike.Lib.LowerX64.Start2W2
import Spike.Lib.LowerX64.Stk2
import Spike.Lib.LblArena

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64 (AS)
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.AllocReach (Reach)

/-- **No placed label covers a runtime word** when every placed label lies
inside the arena `ar` (`LblArena`) and the runtime's words are off it. -/
theorem rtFree_ofArena {L : Spike.Lib.X64.Rt.RuntimeLayout} {ar : Arena} {lbl : Lbl} {lsize : Lsize}
    (hL : LblArena ar lbl lsize) (hoff : ∀ a ∈ L.rtWords, ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells)) :
    Spike.Lib.X64.Rt.RtFree L lbl lsize := by
  rintro a ha ⟨l, b, hl, hc⟩
  have := hL l b hl
  have := hoff a ha
  simp only [lrange, Range.contains] at hc
  omega

open Spike.Lib.X64.Flow.Ret0 (LimOk) in
/-- **`limOk_toAX` at any frames** and any owned words: `msOfAX` shares
`rt`, `mp`, `G` with `msOf` at every frame list. -/
theorem limOk_toAXF {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Own} {own' : OwnS} {ar : Arena} {J : InvS} {ab : Option (State → Prop)}
    {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {F : MachineData → Prop} {a Z : BitVec 64}
    (h : LimOk (msOf Λ μ rd G own lbl lsize) F a Z) :
    LimOk (msOfAX Λ μ p rd G own' ar J ab lbl lsize fs) F a Z := by
  cases ab <;> exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

/-- The output's loaded memory. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

/-- **No placed label covers a runtime word at any level**: at every
placement reachable by allocations in the output's arena `arOf` from the
empty one. -/
theorem rtFree_lvl_ofPlaceOK {lbl : Lbl} {lsize : Lsize}
    (hR : Reach (Spike.Lib.X64.Rt.arOf Λ) (fun _ => none) (fun _ => 0) lbl lsize) :
    Spike.Lib.X64.Rt.RtFree (Ly) lbl lsize :=
  rtFree_ofArena ((LblArena.none _ _).reach hR) (rtWords_offArena h i)

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.PhRec (GOf) in
/-- **The limit word's facts at any level** (`limOk_ofPlaceOK` at depth):
under the rows' memory side at a placement reachable from the empty one in
the output's arena (`hR`), at any frames `fs`, any arena `ar`, family `J`
and abort phase `ab`, for any bound `Z` at least the limit (the first
stack's base plus the guard), at the runtime's frame condition. -/
theorem limOk_lvl_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {ar : Arena} {J : InvS}
    {ab : Option (State → Prop)} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
    (hR : Reach (Spike.Lib.X64.Rt.arOf Λ) (fun _ => none) (fun _ => 0) lbl lsize)
    {Z : BitVec 64} (hZ : (Ly).stacksA.toNat + 4096 ≤ Z.toNat) :
    LimOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
        ar J ab lbl lsize fs) (Spike.Lib.X64.Rt.rtF (Ly))
      (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) Z := by
  rw [(Ly).lab_pin]
  exact limOk_toAXF (own := fun s => Spike.Lib.X64.PhRec.own (Ly) s)
    (Spike.Lib.X64.Rt.rt_limOk (rtFree_lvl_ofPlaceOK h i hR) (Spike.Lib.X64.PhRec.room_of_le h i hZ))

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.PhRec (GOf) in
/-- **A callee's prologue limit facts at any level** (`limOk_callee_ofStk`
under the rows' memory side): at a placement reachable from the empty one
(`hR`), at any frames, under a frame condition within `rtF` (`hF`), at a
state at the first thread's `%fs` base (`hfs`) with the stack-depth bound at
the first stack's limit (`hZ`). -/
theorem limOk_callee_lvl {p : Prog} {rd : TermRun.Word → Prop} {ar : Arena} {J : InvS}
    {ab : Option (State → Prop)} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
    (hR : Reach (Spike.Lib.X64.Rt.arOf Λ) (fun _ => none) (fun _ => 0) lbl lsize)
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    {σ : AS} (hfs : σ.regs.fsBase = tpOf (pinA (Ly).lab + 0#64 + 8#64)) {fsz : Int}
    (hZ : StkRoomX ((Ly).stacksA.toNat + 4096) σ fsz) :
    LimOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
        ar J ab lbl lsize fs) F (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec) :=
  limOk_fsBase hfs ((limOk_lvl_ofPlaceOK h i hR hZ).mono hF)

end Place

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.rtFree_ofArena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.rtFree_ofArena

/-- info: 'Spike.Lib.LowerX64.limOk_toAXF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limOk_toAXF

/-- info: 'Spike.Lib.LowerX64.rtFree_lvl_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.rtFree_lvl_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.limOk_lvl_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limOk_lvl_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.limOk_callee_lvl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limOk_callee_lvl
