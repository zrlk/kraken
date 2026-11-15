/-
**A plain callee's prologue inside `W2` at a base context** (x86-64; the
twin of `Spike/Lib/LowerA64/G1ProCallG2.lean`): `ProCallG2`
(`Spike/Lib/LowerX64/G1CallG2.lean`), the callee's prologue at its entry
invariant `calleeJSO`, in its region `calleeR (rbR R) size D` below the
caller's frame and saved `%rbp`, at the call's frame pushed on the caller's
frames.

- `proCallG2`: from the room and limit statements (`Room2OwnStmt`,
  `Room2CalleeStmt`, `Lim2CalleeStmt`): the callee's context
  (`CxG2M.callG2`, at the callee's rebased region), the callee's region's
  facts from the caller's context (`calleeR_ok`, `stackOff_callee`), its
  prologue inside `W2` placed under its frame condition (`proW_w2F`), the
  abort phase (`proW_abStC`), the limit word mapped (`hmr_TP0`), the entry
  placed from `%rdi` and the caller's frames (`placedS_calleeEntry`).
-/
import Spike.Lib.LowerX64.G1CallG2
import Spike.Lib.LowerX64.G1ProW
import Spike.Lib.LowerX64.G1CalleePlace
import Spike.Lib.LowerX64.G1Hmr

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1ProCall

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A plain callee's prologue inside `W2` at a base context**
(`ProCallG2`): the callee's context with the caller's record pushed
(`CxG2M.callG2`) gives its frame condition's thread pointer, limit word,
room and placement; the callee's region `calleeR (rbR R) size D` is a
region (`calleeR_ok`) 8-aligned, below the callee's frame and saved
`%rbp` (its room, `Room2OwnStmt`), its stack words off it from the
caller's (`stackOff_callee`); the prologue inside `W2` (`proW_w2F`) at the
block's prologue facts (`ProOK`, `fnCode2OfPMe_spec`), its abort phase
(`proW_abStC`, the overflow target off the write abort, `posOff_proL_FC`),
the limit word mapped (`hmr_TP0`, the thread pointer the first TCB's), the
entry's states placed from `%rdi` on the call's frame and the caller's
frames (`placedS_calleeEntry`), the entry control `q.cE` free of `ZBad` at
the frames (the callee's ghosts). -/
theorem proCallG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) : ProCallG2 h hp := by
  intro Dt J j d hd R F fs fp ra tp G0 Ab hcx hra D hDe g q frm F' hF' hCF hex hav hbl hsite j' dg hd' hf
  have hc' := (CxG2M.callG2 h hp hown hrc hlc hd hcx hDe hF' hCF hex hsite hd' hf).1.1
  have hc := hcx.1
  have hR := hc.hR
  have hR8 := hc.hR8
  have hl := hc.hl
  have hh := hc.hh
  have hhi := hc.hhi
  have h16 := (FC j d hd).h16
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
  have hlo' : (calleeR (rbR R) (FC j d hd).fr.size D).lo ≤ -8 - ((FC j' dg hd').fr.size : Int) := by
    have := hown j' dg hd' 256 _ (hc'.room dg hd')
    simp only [rbR, calleeR, Region.callee] at this ⊢
    omega
  have hhi' : (0 : Int) ≤ (calleeR (rbR R) (FC j d hd).fr.size D).hi := by
    simp only [calleeR, Region.callee]; omega
  have hl' : (calleeR (rbR R) (FC j d hd).fr.size D).lo % 8 = 0 := by
    simp only [calleeR, Region.callee]; omega
  have hh' : (calleeR (rbR R) (FC j d hd).fr.size D).hi % 8 = 0 := by
    simp only [calleeR, Region.callee]; omega
  have hFO' : ∀ m, F' m → StackOff (rS0 (Ly)) (calleeR (rbR R) (FC j d hd).fr.size D) m := fun m hm =>
    Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by omega) (by omega) (by omega)
      (hc.hFO m (hCF m hm).1) (hCF m hm).2.1
  -- the callee block's prologue facts
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  obtain ⟨hfr, hen, hph, hent⟩ := (fnCode2OfPMe_spec hp h Λ j' dg hd').2.2
  have hE : PosOff (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).prog
      (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab
      ((Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (FC j' dg hd').entry) :=
    hen ▸ posOff_labelOf_user (hen ▸ hent)
  have htp : ∀ σ c, calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F'
      (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).exe).label
      g tp q σ c → σ.regs.fsBase = tp :=
    fun σ c hJ => hJ.1.2.2.2.2
  have hab := proW_abStC (FC j' dg hd')
    (ms := MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) (frm :: fs)) hI
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfr (posOff_proL_FC hp h Λ j' dg hd' _) hE htp hRc
    (by omega) hhi' hc'.hun
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false ⟨limA tp, 8⟩ = true := by
    rw [hc'.htp]; exact hmr_TP0 h
  refine proW_w2F (FC j' dg hd') hI htp hph hRc hR8' (by omega) hhi' hl' hh' hmr hc'.hun
    (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub (Ly) (Spike.Lib.X64.Rt.rS0_sub (Ly))) hFO'
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hF' hab ?_ ?_
  · intro σ c hJ s hF ha
    exact placedS_calleeEntry h (FC j d hd).hf hCF hlo hhi hD0 hc.hfp hav _ g tp _ σ c hJ s hF ha
  · rintro σ c ⟨⟨rfl, -⟩, -⟩
    exact ⟨fun h' => absurd h' (List.cons_ne_nil _ _), hc'.hG0F q.cE (.refl _)⟩

end G1ProCall

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.proCallG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proCallG2
