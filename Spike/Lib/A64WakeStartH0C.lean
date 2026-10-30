/-
**The start's heap-abort exit closes** (AArch64): from
`StartH0G.wake_start_wc_h0W`'s exit (`wc_main`'s `wX .abort` at the switched
region, any `v`, `m0`, `σC`), the heap abort runs inside wake's level before
the allocation (`WakeWf.W0` at `ownG`, `arW`, `ClW`, `X0W … (aW E)`) under
the take move `PhRec.K`, and never exits (`False`): `HAbStubK.wc_heapAbStubK`
in the region of `wc_main` after the switch (only `v` at the stack's top
occurs, `swF`), `WakeWc.wc_heapAb_segWS`.

- `wake_hab_closed`: the exit's pairs at the frames `[]` start a segment
  with no exit, at the memory side `msOfA` of the entry's marks (any `rd`,
  `G`, `own`, `I`, `ls`). Premises: the loader's facts (`hpa`, `hwp`,
  `hlo0`) and `c0W`'s placement (`hpl0`).
-/
import Spike.Lib.A64WakeHAbStubK
import Spike.Lib.A64WakeStartH0G
import Spike.Lib.A64WakeAbOffW

namespace Spike.Lib.A64.WakePh.StartH0C

open Spike.Lib.A64.WakePh.HAbStubK (wc_heapAbStubK hctl_c0W x0W_abort)
open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi textProgram)
open Spike.Lib (Arena FragS Region SegWS HeapAbortOblA)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At swR)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcHAbStub AGB wX)
open Spike.Lib.A64.Abort.Disp (HPathW)
open Spike.Lib.A64.WakeWf (DtW W0 RunWf X0W)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakePh.WcW (cv inCv)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ) rd G own
  (Spike.Lib.WakeOD.arW hpw i) I (L0T (Ly).Λ) ls fs

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

/-- **The start's heap-abort exit closes** (`StartH0B`'s `hC`): from
`wake_start_wc_h0W`'s exit at the frames `[]`, a segment inside `W0` at
`ownG`, `arW`, `ClW`, `X0W … (aW E)` under the take move, with no exit. -/
theorem wake_hab_closed {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isaLSE2} {ls0 : Lsize} {frM : TermRun.Frame}
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = lo)
    /- named premise: `c0W` placed at every state -/
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W []) :
    SegWS (W0 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab))
        (Spike.Lib.WakeOD.arW hpw i) wakeSrc DtW (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (Spike.Lib.WakeOD.ClW hpw i)
        (Spike.Lib.A64.ThreadsAb.Ac (Ly).lab pfxM) Ctx (L0T (Ly).Λ) (ls0T ls0) frM
        (X0W (Ly) (Spike.Lib.WakeOSide.aW hpw i E)))
      (Spike.Lib.A64.PhRec.K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) wakeSrc (L0T (Ly).Λ) (MSf)
      (Spike.Lib.Frag.at (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
          (wF (swR v (-384) 0) 336 (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC)
          (wX ((MSf) []) (Ly).lab ((JW) σC) .abort) s c ∧
        Spike.Lib.A64.KeepTP.TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s) [])
      (fun _ _ _ => False) := by
  have hp := Spike.Lib.A64.WakePh.StartPlaceLy.hp_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hpw i hlo0
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hpw i hpa hwp
  have hpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hax : (Spike.Lib.WakeOSide.aW hpw i E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.WakeOSide.aW_site hpw i hpa hwp hpL (Spike.Lib.PlaceW.site_ofPlaceW hpw i) E]
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hab : ∀ s : State, s.st.2 = (Ly).lab "scc_rt_abort_heap_exit" → ((MSf) []).abortAt s := fun s hs => by
    obtain ⟨-, -, -, -, -, -, -, -, e9, -⟩ := abH_labs hlab
    refine ⟨.heap, 2168332, ?_, by rw [pcOf, hs, e9]; rfl⟩
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
    show codeOf (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
    rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × Spike.Lib.A64.Flow.AS =>
      Spike.Lib.Frag.at (At (Ly).exe (Ly).endPc (wR (swR g.1 (-384) 0) 336)
        (wF (swR g.1 (-384) 0) 336 (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 g.1) g.2.1 g.2.2)
        (wX ((MSf) []) (Ly).lab ((JW) g.2.2) .abort)) []) fun ⟨v, m0, σC⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m0, σC, h, _⟩, hf⟩ => ⟨⟨v, m0, σC⟩, h, hf⟩
  by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv hF.1.2.1.1
  subst hv
  have hF0 := Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)))
    (v := Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) hwf hsub hok (by decide) (by decide)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
        exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
  obtain ⟨hR, hal, hF⟩ := Spike.Lib.A64.Flow.WakeM.wR_ok (D := 336) (by decide) (by decide) hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _) hF0
    (by show (-384 : Int) ≤ -48 - 336; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
  exact Spike.Lib.A64.Flow.WakeWc.wc_heapAb_segWS hF hR hal (by show (-336 : Int) ≤ -288; decide)
    (by show (0 : Int) ≤ 0; decide) rfl
    (wc_heapAbStubK hprog hlo hlab _ hΛ hF hR hal (by show (-336 : Int) ≤ -288; decide)
      (by show (0 : Int) ≤ 0; decide) rfl (.inl rfl) (fun _ h => h.2)
      (hctl_c0W rfl rfl rfl hpl0) hab (x0W_abort hlab hax)) _

end Place

end Spike.Lib.A64.WakePh.StartH0C

/-- info: 'Spike.Lib.A64.WakePh.StartH0C.wake_hab_closed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0C.wake_hab_closed
