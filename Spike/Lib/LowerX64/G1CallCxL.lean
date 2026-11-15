/-
**A base context at a reachable placement is kept by a plain call**
(x86-64; the twin of `Spike/Lib/LowerA64/G1CallCxL.lean`): `CxCore2.call`
(`Spike/Lib/LowerX64/G1CallCx.lean`) at `CxCore2L`
(`Spike/Lib/LowerX64/G1FnSpecL.lean`), the callee at the caller's
placement.

- `MSAtL.rd_frames`, `MSAtL.K_frames`: `MSAtL`'s readable words and ABI do
  not depend on the frames;
- `CxCore2L.call`: the closure.
-/
import Spike.Lib.LowerX64.G1CallCx
import Spike.Lib.LowerX64.G1FnSpecL

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (FStable)
open Spike.Lib.X64.Flow (CallTo)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

/-- `MSAtL`'s readable words do not depend on the frames. -/
theorem MSAtL.rd_frames {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : Expr → String → Nat → Option Nat) (p : Prog) (rd : TermRun.Word → Prop)
    (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize) (L : Lbl) (ls : Lsize) (fs fs' : List TermRun.Frame) :
    (MSAtL h i p rd J ab ls0 L ls fs).rd = (MSAtL h i p rd J ab ls0 L ls fs').rd := by
  cases ab <;> rfl

/-- `MSAtL`'s ABI does not depend on the frames. -/
theorem MSAtL.K_frames {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : Expr → String → Nat → Option Nat) (p : Prog) (rd : TermRun.Word → Prop)
    (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize) (L : Lbl) (ls : Lsize) (fs fs' : List TermRun.Frame) :
    (MSAtL h i p rd J ab ls0 L ls fs).K = (MSAtL h i p rd J ab ls0 L ls fs').K := by
  cases ab <;> rfl

section G1CallL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`) and the
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
    {D : Int} (hD : 8 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -((FC j d hd).fr.size : Int) - 8 - D)
    {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR R (FC j d hd).fr.size D) F')
    (hCF : CalleeF2 p L ls (FC j d hd).fr R F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F')
    (hcall : ∃ c, G0 c ∧ CallTo p c q.cE frm)
    {j' : Nat}
    (hroom : ∀ dg, (compiled2 p)[j']? = some dg →
      NeedRoomX (OUT).place.need (Scc.Lower.Names.user dg.name) 256 (-D))
    (hlim : ∀ m, F' m → ∀ dg, (compiled2 p)[j']? = some dg →
      LimRoomX (OUT).place.need (Scc.Lower.Names.user dg.name) (((MSL J L ls) []).G ⟨limA tp, 8⟩)
        (R.base.toNat - (FC j d hd).fr.size - 8))
    (hown : ∀ dg (hdg : (compiled2 p)[j']? = some dg) (s : Nat) (lo : Int),
      NeedRoomX (OUT).place.need (Scc.Lower.Names.user dg.name) s lo →
        lo ≤ -(((FC j' dg hdg).fr.size : Int) + 8 + s))
    (hnb : ¬ HasNewBuf2 p j') :
    CxCore2L h hp Dt J L ls j' (rbR (calleeR R (FC j d hd).fr.size D)) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) := by
  have hR := hc.hR
  have hR8 := hc.hR8
  have hal := hc.hal
  have hl := hc.hl
  have hh := hc.hh
  have hhi := hc.hhi
  have h16 := (FC j d hd).h16
  have hf := (FC j d hd).hf
  -- the callee's region `calleeR R size D` and its rebased one
  have hcb := Region.callee_base (hi' := 8) hR (kc := -((FC j d hd).fr.size : Int) - 8) (lo' := -D)
    (by omega) (by omega) (by omega)
  have hRc : (calleeR R (FC j d hd).fr.size D).OK := calleeR_ok hR (by omega) hlo (by omega)
  have hloc : (calleeR R (FC j d hd).fr.size D).lo ≤ -8 := by simp only [calleeR, Region.callee]; omega
  have hhic : (0 : Int) ≤ (calleeR R (FC j d hd).fr.size D).hi := by simp only [calleeR, Region.callee]; omega
  have hb := rbR_base hRc hloc hhic
  have hb' : ((calleeR R (FC j d hd).fr.size D).base.toNat : Int) = R.base.toNat + (-((FC j d hd).fr.size : Int) - 8) :=
    hcb
  have hnoS := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hE : FrOk2 q.cE (frm :: fs) := by
    obtain ⟨c, hc0, hct⟩ := hcall
    exact Spike.Lib.LowerNode.FrOk2.run hnoS (FrameRun.single (hct.step fs)) (hc.hG0F c hc0)
  refine
    { hre := hc.hre
      hR := rbR_ok hRc hloc hhic
      hR8 := by omega
      hal := by omega
      hl := by simp only [rbR, calleeR, Region.callee]; omega
      hh := by simp only [rbR, calleeR, Region.callee]; omega
      hhi := by simp only [rbR, calleeR, Region.callee]; omega
      hFS := rbR_fstable hRc hloc hhic hF'
      hFO := fun m hm => stackOff_rbR hRc hloc hhic
        (Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by omega) (by omega) (by omega)
          (hc.hFO m (hCF m hm).1) (hCF m hm).2.1)
      hrs := ?_
      hfp := framesPlaced_calleeF2 (Λ := (Ly).Λ) hf hCF hlo hhi (by omega) hc.hfp
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
      room := ?_
      lim := ?_
      htp := hc.htp
      hun := fun m hm => hc.hun m (hCF m hm).1 }
  · intro dg hdg r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds (FC j' dg hdg).hf hk
    have := hown dg hdg 256 (-D) (hroom dg hdg)
    simp only [Region.Off, rbR, calleeR, Region.callee]
    omega
  · intro dg hdg
    have e : (rbR (calleeR R (FC j d hd).fr.size D)).lo - 8 = -D := by
      simp only [rbR, calleeR, Region.callee]; omega
    rw [e]
    exact hroom dg hdg
  · intro m hm dg hdg
    have e : (rbR (calleeR R (FC j d hd).fr.size D)).base.toNat + 8 = R.base.toNat - (FC j d hd).fr.size - 8 := by
      omega
    rw [e]
    exact hlim m hm dg hdg

end G1CallL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.CxCore2L.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CxCore2L.call
