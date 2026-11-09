/-
**The heap-abort exit closes at any placement** (AArch64):
`StartH0C.hello_hab_closed` with the start's placement `L0T (Ly).Λ` and sizes `ls0T ls0` generalised to any `LB`,
`ls0` (its proof never reads them: the stub `HAbStub.wc_heapAbStubKH` is generic in `L0`, `ls0`, and the memory
side's abort facts do not depend on the placement). Level 1 closes `wc_main`'s box allocation's heap abort with it
at `LB := upd (L0T (Ly).Λ) l b`, `ls0 := updN (ls0T ls) l n` (`HelloWf.W1H` is `WS` there by definition).

- `hello_hab_closedL`: the statement. Premises: the loader's facts (`hpa`, `hhp`, `hlo0`) and the
  controls' facts at `wXH .abort` at the placement `LB` (`hhabctl`, `HabCtl.HabCtlH`).
-/
import Spike.Lib.A64HelloHabCtl
import Spike.Lib.A64HelloStartH0G
import Spike.Lib.A64WakeAbOffW

namespace Spike.Lib.A64.HelloPh.StartH0CL

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi textProgram)
open Spike.Lib (Arena FragS Frag Region SegWS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib.A64.HelloPh.HAbStub (wc_heapAb_segWSH wc_heapAbStubKH x0WH_abort)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd G own
  (Spike.Lib.WakeOD.arW hpw i) I LB ls fs

set_option hygiene false in
/-- `wc_main`'s entry invariant below the call of `wc_main` at the caller's state `σC`. -/
local notation "JC" => fun v m0 σC σ1 => wcJ0 (mWC (Ly).lab σC (Jr1 v m0 σC)).J σ1

/-- **The heap-abort exit closes at any placement `LB`, sizes `ls0`** (`StartH0C.hello_hab_closed`'s proof
verbatim): from `wc_main`'s `wXH .abort` exit at the frames `[]`, a segment inside `W0` at `ownGH`, `arW`, `ClH`,
`DtW`, `X0WH … (lab take_site)`, the labels `LB`, under the take move, with no exit. -/
theorem hello_hab_closedL {LB : Lbl} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isaLSE2} {ls0 : Lsize} {frM : TermRun.Frame} {t : UInt64}
    {Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    /- named premise: the controls' facts at `wXH .abort` -/
    (hhabctl : ∀ v m0 σC σ1, HabCtlH ((MSf) []) (Ly).lab helloSrc (Ly).Λ LB (Spike.Lib.WakeOD.arW hpw i)
      [] ((JC) v m0 σC σ1)) :
    SegWS (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hpw i) helloSrc DtW
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx LB ls0 frM
        (X0WH (Ly) ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL)))
      (Spike.Lib.A64.PhRec.K (Ly) RS) helloSrc LB (MSf)
      (Frag.at (fun s c => ∃ v m0 σC m1 σ1,
        At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
          (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) RS helloLsw 0#64 v) m1 σ1)
          (wXH ((MSf) []) (Ly).lab ((JC) v m0 σC σ1) .abort) s c ∧ Spike.Lib.A64.KeepTP.TP t s) [])
      (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hab : ∀ s : State, s.st.2 = (Ly).lab "scc_rt_abort_heap_exit" → ((MSf) []).abortAt s := fun s hs => by
    obtain ⟨-, -, -, -, -, -, -, -, e9, -⟩ := Spike.Lib.A64.HelloPh.abH_labsH hlab
    refine ⟨.heap, 2168400, ?_, by rw [pcOf, hs, e9]; rfl⟩
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
    show codeOf (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
    rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS × MachineData × FAS =>
      Frag.at (At (Ly).exe (Ly).endPc (wcR (swR g.1 (-helloLsw) 0) helloD)
        (wcF (swR g.1 (-helloLsw) 0) helloD (FS (Ly) RS helloLsw 0#64 g.1) g.2.2.2.1 g.2.2.2.2)
        (wXH ((MSf) []) (Ly).lab ((JC) g.1 g.2.1 g.2.2.1 g.2.2.2.2) .abort)) [])
      fun ⟨v, m0, σC, m1, σ1⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m0, σC, m1, σ1, h, _⟩, hf⟩ => ⟨⟨v, m0, σC, m1, σ1⟩, h, hf⟩
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
  obtain ⟨hR, hal, hF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _) hF0
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  exact wc_heapAb_segWSH hF hR hal (by show (-helloD : Int) ≤ -352; decide)
    (by show (0 : Int) ≤ 0; decide) rfl
    (wc_heapAbStubKH hprog hlo hlab _ hΛ hF hR hal (by show (-helloD : Int) ≤ -352; decide)
      (by show (0 : Int) ≤ 0; decide) rfl (.inl rfl) (fun _ h => h.2)
      (hhabctl _ m0 σC σ1).hctl hab (x0WH_abort hlab rfl)) _

end Place

end Spike.Lib.A64.HelloPh.StartH0CL

/-- info: 'Spike.Lib.A64.HelloPh.StartH0CL.hello_hab_closedL' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0CL.hello_hab_closedL
