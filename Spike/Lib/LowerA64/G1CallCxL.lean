/-
**A base context at a reachable placement is kept by a plain call**
(AArch64): `CxCore2.call` (`Spike/Lib/LowerA64/G1CallCx.lean`) at
`CxCore2L` (`Spike/Lib/LowerA64/G1FnSpecL.lean`), the callee at the
caller's placement.

- `MSAtL.rd_frames`, `MSAtL.K_frames`: `MSAtL`'s readable words and ABI do
  not depend on the frames;
- `CxCore2L.call`: the closure.
-/
import Spike.Lib.LowerA64.G1CallCx
import Spike.Lib.LowerA64.G1FnSpecL

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

/-- `MSAtL`'s readable words do not depend on the frames. -/
theorem MSAtL.rd_frames {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : Expr → String → Nat → Option Nat) (p : Prog) (rd : TermRun.Word → Prop)
    (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize) (L : Lbl) (ls : Lsize) (fs fs' : List TermRun.Frame) :
    (MSAtL h i p rd J ab ls0 L ls fs).rd = (MSAtL h i p rd J ab ls0 L ls fs').rd := by
  cases ab <;> rfl

/-- `MSAtL`'s ABI does not depend on the frames. -/
theorem MSAtL.K_frames {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : Expr → String → Nat → Option Nat) (p : Prog) (rd : TermRun.Word → Prop)
    (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize) (L : Lbl) (ls : Lsize) (fs fs' : List TermRun.Frame) :
    (MSAtL h i p rd J ab ls0 L ls fs).K = (MSAtL h i p rd J ab ls0 L ls fs').K := by
  cases ab <;> rfl

section G1CallL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`) and the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A plain call keeps the base context at a reachable placement**
(`CxCore2.call` at `CxCore2L`, the callee at the caller's placement `L`,
`ls`): the same premises with the call's frame condition `CalleeF2` at
`L`, `ls` and the limit rows at `MSAtL … L ls`. -/
theorem CxCore2L.call (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} {J : InvS}
    {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {j : Nat}
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} (hc : CxCore2L h hp Dt J L ls j R F fs fp ra tp G0) {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -((FC j d hd).cx.frame : Int) - D)
    {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F')
    (hCF : CalleeF2 p L ls (FC j d hd).cx R F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F')
    (hcall : ∃ c, G0 c ∧ CallTo p c q.cE frm)
    {j' : Nat}
    (hroom : ∀ dg, (compiled2 p)[j']? = some dg →
      NeedRoomA (OUT).place.need (Scc.Lower.Names.user dg.name) 256 (-D))
    (hlim : ∀ m, F' m → ∀ dg, (compiled2 p)[j']? = some dg →
      LimRoomA (OUT).place.need (Scc.Lower.Names.user dg.name) (((MSL J L ls) []).G ⟨limA tp, 8⟩)
        (R.base.toNat - (FC j d hd).cx.frame))
    (hown : ∀ dg (hdg : (compiled2 p)[j']? = some dg) (s : Nat) (lo : Int),
      NeedRoomA (OUT).place.need (Scc.Lower.Names.user dg.name) s lo →
        lo ≤ -(((FC j' dg hdg).cx.frame : Int) + s))
    (hnb : ¬ HasNewBuf2 p j') :
    CxCore2L h hp Dt J L ls j' (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) := by
  have hR := hc.hR
  have hal := hc.hal
  have hl := hc.hl
  have hh := hc.hh
  have hhi := hc.hhi
  have h16 := (FC j d hd).h16
  have hf := (FC j d hd).hf
  have hpos : 0 < (FC j d hd).cx.frame := by
    have := Scc.Lower.InvA64.align16_mod (8 * (FC j d hd).cx.slots.length + 16)
    have := Scc.Lower.InvA64.le_align16 (8 * (FC j d hd).cx.slots.length + 16)
    unfold Scc.Lower.InvA64.FrameOk at hf
    omega
  have hcb := Region.callee_base (hi' := 0) hR (kc := -((FC j d hd).cx.frame : Int)) (lo' := -D)
    (by omega) (by omega) (by omega)
  have hnoS := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hE : FrOk2 q.cE (frm :: fs) := by
    obtain ⟨c, hc0, hct⟩ := hcall
    exact Spike.Lib.LowerNode.FrOk2.run hnoS (FrameRun.single (hct.step fs)) (hc.hG0F c hc0)
  refine
    { hre := hc.hre
      hR := Region.callee_ok hR (by omega) (by omega) (by omega) (by omega)
      hal := ?_
      hl := by simp only [Region.callee]; omega
      hh := by simp only [Region.callee]; omega
      hhi := by simp only [Region.callee]; omega
      hFS := hF'
      hFO := fun m hm => Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR (by omega) hl hh (by omega) (by omega) (by omega) (by omega)
        (hc.hFO m (hCF m hm).1) (hCF m hm).2.1
      hrs := ?_
      hfp := framesPlaced_calleeF2 (Λ := (Ly).Λ) hf hCF hlo hhi hD0 hc.hfp
      hes := fun m hm f hf' => by
        rcases List.mem_cons.mp hf' with rfl | hf'
        · exact envSmall_calleeF2 hCF m hm
        · exact hc.hes m (hCF m hm).1 f hf'
      hfs := fun _ => List.cons_ne_nil _ _
      hrd := MSAtL.rd_frames h _ p IsNum J _ _ L ls fs (frm :: fs) ▸ hc.hrd
      hwn := fun m hm => hc.hwn m (hCF m hm).1
      hG0F := fun c0 hr => Spike.Lib.LowerNode.FrOk2.runM hnoS hr hE
      hG0 := fun c c' h1 h2 => h1.trans h2
      hK := MSAtL.K_frames h _ p IsNum J _ _ L ls fs (frm :: fs) ▸ hc.hK
      hAW := fun _ _ hn => absurd hn hnb
      room := hroom
      lim := ?_
      htp := hc.htp
      hun := fun m hm => hc.hun m (hCF m hm).1 }
  · show (R.addr (-((FC j d hd).cx.frame : Int))).toNat % 16 = 0
    simp only [Region.callee] at hcb
    omega
  · intro dg hdg r k hk
    obtain ⟨hk8, hk1, hk2, -⟩ := rsOf_cell (FC j' dg hdg).hf hk
    have := hown dg hdg 256 (-D) (hroom dg hdg)
    simp only [Region.Off, Region.callee]
    omega
  · intro m hm dg hdg
    have hb : (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0).base.toNat =
        R.base.toNat - (FC j d hd).cx.frame := by omega
    rw [hb]
    exact hlim m hm dg hdg

end G1CallL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.CxCore2L.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxCore2L.call
