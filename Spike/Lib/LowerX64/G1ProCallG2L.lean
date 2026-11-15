/-
**A plain callee's prologue inside `W2` at a base context and a reachable
placement** (x86-64; the twin of `Spike/Lib/LowerA64/G1ProCallG2L.lean`):
`ProCallG2` (`Spike/Lib/LowerX64/G1CallG2.lean`) with the current placement
`L`, `ls` a parameter (`CxG2ML`, `W2AtL`, `MSAtL`,
`Spike/Lib/LowerX64/G1FnSpecL.lean`).

- `ProCallG2L`: the statement, `ProCallG2`'s binders with `L`, `ls` after
  `J`;
- `proCallG2L_core`: the prologue from the caller's facts `CxCore2L` only
  (the callee's region `calleeR (rbR R) size D`, frame condition, limit
  word and room from the caller's, its placement from `%rdi` and the
  caller's frames);
- `proCallG2L`: `ProCallG2L` from the room and limit statements;
- `proCallG2_ofL`: `ProCallG2` at the start's placement (`CxCore2.toL`).
-/
import Spike.Lib.LowerX64.G1FnSpecL
import Spike.Lib.LowerX64.G1CallG2
import Spike.Lib.LowerX64.G1ProW
import Spike.Lib.LowerX64.G1CalleePlace
import Spike.Lib.LowerX64.G1Hmr

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0 argXs)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1ProCallL

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
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- `W2AtL` at `Closed2At`'s instance and the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`) and the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.X64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The code facts' return address condition. -/
local notation "RAOK" ra:max => Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat

set_option linter.unusedVariables false in
/-- **A callee's prologue inside `W2` at a plain call and a reachable
placement** (`ProCallG2`'s at `L`, `ls`): at a plain call of `g` in the
`j`th compiled block under a base context at any frames and the placement
`L`, `ls` (`CxG2ML`), at the caller's depth `D` (below its frame and saved
`%rbp` in the rebased region), the callee `dg` found for `g` the `j'`th
compiled block, its prologue inside `W2AtL … L ls` at the entry invariant
`calleeJSO` in its region `calleeR (rbR R) size D`. -/
def ProCallG2L (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat)
    (j : Nat) (d : Decl)
    (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa),
    CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab → RAOK ra →
    ∀ (D : Int), (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D →
    ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
    FStable (calleeR (rbR R) (FC j d hd).fr.size D) F' →
    CalleeF2 p L ls (FC j d hd).fr (rbR R) F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F' →
    (∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm) →
    ArgV L q →
    (∃ pcB zc k, (FC j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
    CallSite2F p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) G0
      (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p) (RetLk d.retTy) g q (rbR R) D fp ra
      frm F' →
    ∀ (j' : Nat) (dg : Decl) (hd' : (compiled2 p)[j']? = some dg), p.find? (·.name == g) = some dg →
    XProW (fun s c => (W2L J L ls) s c (frm :: fs)) (KT) (LY0).exe (LY0).endPc
      (calleeR (rbR R) (FC j d hd).fr.size D) F' ((MSL J L ls) (frm :: fs))
      ((_root_.Executable.labels (LY0).exe).label (FC j' dg hd').fn) (Int64.ofInt (FC j' dg hd').fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (FC j' dg hd').fr) (FC j' dg hd').zl (FC j' dg hd').zf
      (FC j' dg hd').z1 (FC j' dg hd').z2 (FC j' dg hd').zs (FC j' dg hd').ps
      (calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F' (_root_.Executable.labels (LY0).exe).label g tp q)


/-- **A plain callee's prologue inside `W2` from the caller's facts** (at a
reachable placement `L`, `ls`): from the caller's `CxCore2L` at the `j`th
compiled block in its rebased region `rbR R`, at the caller's depth `D`
(below its frame and saved `%rbp`), the callee's region
`calleeR (rbR R) size D` (its bounds from the caller's), frame condition
`F'` (`CalleeF2`: the caller's, so the stack's offsets, the limit word
unmapped), the callee's room at `-D` (`Room2CalleeStmt`) covering its frame
and saved `%rbp` (`Room2OwnStmt`), the entry control `q.cE` free of `ZBad`
after the call's step: the prologue inside `W2` (`proW_w2F`), its abort
phase (`proW_abStC`), the limit word mapped (`hmr_TP0`), the entry placed
from `%rdi` on the call's frame and the caller's frames
(`placedS_calleeEntryG`). -/
theorem proCallG2L_core (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp)
    {Dt : State → Prop} {J : InvS} {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    (hc : CxCore2L h hp Dt J L ls j (rbR R) F fs fp ra tp G0)
    {D : Int} (hDe : (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D)
    {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) (FC j d hd).fr.size D) F')
    (hCF : CalleeF2 p L ls (FC j d hd).fr (rbR R) F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F')
    (hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (hav : ArgV L q)
    (hsite : CallSite2F p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) G0
      (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p) (RetLk d.retTy) g q (rbR R) D fp ra
      frm F')
    {j' : Nat} {dg : Decl} (hd' : (compiled2 p)[j']? = some dg) (hf : p.find? (·.name == g) = some dg) :
    XProW (fun s c => (W2L J L ls) s c (frm :: fs)) (KT) (LY0).exe (LY0).endPc
      (calleeR (rbR R) (FC j d hd).fr.size D) F' ((MSL J L ls) (frm :: fs))
      ((_root_.Executable.labels (LY0).exe).label (FC j' dg hd').fn) (Int64.ofInt (FC j' dg hd').fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (FC j' dg hd').fr) (FC j' dg hd').zl (FC j' dg hd').zf
      (FC j' dg hd').z1 (FC j' dg hd').z2 (FC j' dg hd').zs (FC j' dg hd').ps
      (calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F' (_root_.Executable.labels (LY0).exe).label g tp q) := by
  have hR := hc.hR
  have hR8 := hc.hR8
  have hl := hc.hl
  have hh := hc.hh
  have hhi := hc.hhi
  have h16 := (FC j d hd).h16
  have hgn : dg.name = g := by simpa using List.find?_some hf
  obtain ⟨-, -, -, -, -, -, -, x, a, e, -, -, -, -, -, -, -, -, -, hT, -, -, -, -, -, hcl, -⟩ := id hsite
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have hD0 : 0 ≤ D := by omega
  have hlo : (rbR R).lo ≤ -((FC j d hd).fr.size : Int) - 8 - D := by omega
  -- the callee's region `calleeR (rbR R) size D`
  have hRc : (calleeR (rbR R) (FC j d hd).fr.size D).OK := calleeR_ok hR hD0 hlo (by omega)
  have hcb := Region.callee_base (hi' := 8) hR (kc := -((FC j d hd).fr.size : Int) - 8) (lo' := -D)
    (by omega) (by omega) (by omega)
  have hb' : ((calleeR (rbR R) (FC j d hd).fr.size D).base.toNat : Int) =
      (rbR R).base.toNat + (-((FC j d hd).fr.size : Int) - 8) := hcb
  have hR8' : (calleeR (rbR R) (FC j d hd).fr.size D).base.toNat % 8 = 0 := by omega
  have hhi' : (0 : Int) ≤ (calleeR (rbR R) (FC j d hd).fr.size D).hi := by
    simp only [calleeR, Region.callee]; omega
  have hl' : (calleeR (rbR R) (FC j d hd).fr.size D).lo % 8 = 0 := by
    simp only [calleeR, Region.callee]; omega
  have hh' : (calleeR (rbR R) (FC j d hd).fr.size D).hi % 8 = 0 := by
    simp only [calleeR, Region.callee]; omega
  have hFO' : ∀ m, F' m → StackOff (rS0 (Ly)) (calleeR (rbR R) (FC j d hd).fr.size D) m := fun m hm =>
    Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by omega) (by omega) (by omega)
      (hc.hFO m (hCF m hm).1) (hCF m hm).2.1
  have hun' : ∀ m, F' m → Mem.loadInt m.dmem (limA tp) 8 = none := fun m hm => hc.hun m (hCF m hm).1
  -- the callee's room covering its frame and saved `%rbp`
  have hroom : NeedRoomX (OUT).place.need (Scc.Lower.Names.user dg.name) 256 (-D) := by
    obtain ⟨-, -, -, -, -, hr⟩ := hrc j d hd x g a e 256 ((rbR R).lo - 8) hT hcl (hc.room d hd)
    have e2 : (rbR R).lo - 8 + ((FC j d hd).fr.size : Int) + 16 = -D := by omega
    rw [e2] at hr
    rw [hgn]
    exact hr
  have hlo' : (calleeR (rbR R) (FC j d hd).fr.size D).lo ≤ -8 - ((FC j' dg hd').fr.size : Int) := by
    have := hown j' dg hd' 256 _ hroom
    simp only [calleeR, Region.callee]
    omega
  -- the entry control free of `ZBad`
  have hE : FrOk2 q.cE (frm :: fs) := by
    obtain ⟨c, -, -, -, hc0, -, -, hct⟩ := hex
    exact Spike.Lib.LowerNode.FrOk2.run (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp)
      (FrameRun.single (hct.step fs)) (hc.hG0F c hc0)
  -- the callee block's prologue facts
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  obtain ⟨hfr, hen, hph, hent⟩ := (fnCode2OfPMe_spec hp h Λ j' dg hd').2.2
  have hEn : PosOff (LY0).prog (LY0).lab ((LY0).lab (FC j' dg hd').entry) :=
    hen ▸ posOff_labelOf_user (hen ▸ hent)
  have htp : ∀ σ c, calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F'
      (_root_.Executable.labels (LY0).exe).label g tp q σ c → σ.regs.fsBase = tp :=
    fun σ c hJ => hJ.1.2.2.2.2
  have hab := proW_abStC (FC j' dg hd') (ms := (MSL J L ls) (frm :: fs)) hI
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfr (posOff_proL_FC hp h Λ j' dg hd' _) hEn htp hRc
    (by omega) hhi' hun'
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false ⟨limA tp, 8⟩ = true := by
    rw [hc.htp]; exact hmr_TP0 h
  refine proW_w2F (FC j' dg hd') hI htp hph hRc hR8' (by omega) hhi' hl' hh' hmr hun'
    (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub (Ly) (Spike.Lib.X64.Rt.rS0_sub (Ly))) hFO'
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hF' hab ?_ ?_
  · rintro σ c ⟨⟨rfl, -, -, hx0, -⟩, -⟩ s hF ha
    refine placedS_calleeEntryG (FC j d hd).hf hCF hlo hhi hD0 hc.hfp hav s hF ?_
    have h0 : s.st.1.regs.get64 .rdi = σ.regs.get64 .rdi := ha 0 (by decide)
    show s.st.1.regs.get64 .rdi = q.v
    rw [h0]
    exact hx0
  · rintro σ c ⟨⟨rfl, -⟩, -⟩
    exact ⟨fun h' => absurd h' (List.cons_ne_nil _ _), hE⟩

/-- **A plain callee's prologue inside `W2` at a reachable placement**
(`ProCallG2L`): `proCallG2L_core` at the base context's facts. -/
theorem proCallG2L (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (_hlc : Lim2CalleeStmt h hp) : ProCallG2L h hp := by
  intro Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx _ D hDe g q frm F' hF' hCF hex hav _ hsite j' dg hd' hf
  exact proCallG2L_core h hp hown hrc hd hcx.1 hDe hF' hCF hex hav hsite hd' hf

/-- **`ProCallG2` at the start's placement** (`proCallG2L_core` at no label
placed, `CxCore2.toL`). -/
theorem proCallG2_ofL (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (_hlc : Lim2CalleeStmt h hp) : ProCallG2 h hp := by
  intro Dt J j d hd R F fs fp ra tp G0 Ab hcx _ D hDe g q frm F' hF' hCF hex hav _ hsite j' dg hd' hf
  exact proCallG2L_core h hp hown hrc hd (hcx.1.toL h) hDe hF' hCF hex hav hsite hd' hf

end G1ProCallL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.proCallG2L_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proCallG2L_core
/-- info: 'Spike.Lib.LowerX64.proCallG2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proCallG2L
/-- info: 'Spike.Lib.LowerX64.proCallG2_ofL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proCallG2_ofL
