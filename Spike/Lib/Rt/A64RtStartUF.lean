/-
**`scc_rt_start`'s states inside `W`, for any placed output, with an extra
frame `Fw` after the switch** (AArch64): `startAllUW_gen`
(`Spike/Lib/Rt/A64RtStartU.lean`) at `StartAllUWF`
(`Spike/Lib/Rt/A64SegsF.lean`).

- `startAllUWF_gen`: `startAllUW_gen`'s proof, the switch's obligations `hs3`
  at `SwUWF`.
-/
import Spike.Lib.Rt.A64RtPhRec
import Spike.Lib.Rt.A64RtCodeSetup
import Spike.Lib.A64StubFacts
import Spike.Lib.Rt.A64RtStartU
import Spike.Lib.Rt.A64SegsF

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TN TK TI TcbG TiG TakeG TcbW TiW TakeW StackM pinA pnA lockA freeNA nextA stacksA)
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option maxHeartbeats 1600000 in
open StartU PhRecOf PhOfTab in
/-- **`startAllUW_gen` with the extra frame `Fw` after the switch**: the
same obligations up to the switch, the switch's and `scc_rt_main`'s as given
at `Fw ∧ swFSL …` (`hs3`). -/
theorem startAllUWF_gen
    (hrt : Scc.Cert.Rt.A64.rtPhOk (Ly).Λ.code.lo o.prog (Ly).Λ (rtPhTab none) = true)
    {p : Prog} {lbl : Lbl} {ms : MemSide isaLSE2} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {Fw : _root_.Mem 64 → Prop} {n0 k0 : BitVec 64} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS)) (hSMi : FStable (R.callee Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hs3 : SwUWF (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R (fun m => F m ∧ StackM rS m) Fw ms rS
      (pinA (Ly).lab + n0 + 8#64) (stacksA (Ly).lab + k0 + 16384#64) c0 L mc D ZU Post) :
    StartAllUWF (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R F Fw ms rS n0 k0 c0 L mc D ZU Post := by
  subst hn0
  have hI := PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCode0_of_placeOKAt h
  have hl := hlab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => Scc.Cert.Rt.A64.factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (Scc.Cert.Link.A64.codeOf (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = (Ly).lab r := fun _ h => nomatch h
  have hW : ∀ s c, SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c →
      SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt :=
    fun _ _ hs => hs.dt_mono fun _ h => h.elim
  have hpn : pnA (Ly).lab = (Ly).pnA := (Ly).lab_pn
  have hpin : pinA (Ly).lab = (Ly).pinA := (Ly).lab_pin
  have hlk : lockA (Ly).lab = (Ly).lockA := (Ly).lab_lock
  have hfr : freeNA (Ly).lab = (Ly).freeNA := (Ly).lab_freeN
  have hnx : nextA (Ly).lab = (Ly).nextA := (Ly).lab_next
  have h0 : ∃ j < 7, (Ly).pinA + 0#64 = (Ly).pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨⟨-, cb0⟩, cb1⟩, cb2⟩, cb3⟩, cb4⟩ := hst
  have hcl := hrc.call
  simp only [Ret0.startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have htl := hrc.tail
  simp only [Ret0.startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨t0, -⟩, t2⟩, t3⟩, -⟩, -⟩ := htl
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩, ⟨?_, fun g hg j => ?_, ?_, ?_⟩, hs3⟩
  · -- The frame's setup.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cb0 (ofNat4_zero _) Abort.b0_ok hR hal
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk "scc_rt_start" 0 Abort.b0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false b0_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph "scc_rt_start" 0 13) (by simp [startPhTab]))) (by decide)))
  · -- The `adrp`.
    have hs := step_of_factOk hl (hf (.step startE 0) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_pre (si := SI.adrp .X9 sigign) (p := (Ly).lab startE + Int64.ofNat (4 * 0))
      hI cb1 rfl (ofNat4_zero _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 0 13) (by simp [startPhTab]))) (by decide)) hs.2)
  · -- The `add`.
    have hs := step_of_factOk hl (hf (.step startE 1) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_pre (si := SI.addLo12 .X9 .X9 sigign)
      (p := (Ly).lab startE + Int64.ofNat (4 * 1)) hI cb2 rfl rfl (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 1 13) (by simp [startPhTab]))) (by decide)) hs.2)
  · -- The arguments.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cb3
      (startE2 (Ly).lab).symm
      startArgs_ok hR hal (by omega) (by omega)
      (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 2 startArgs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startArgs_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 2 13) (by simp [startPhTab]))) (by decide)))
  · -- The system call.
    have hs := step_of_factOk hl (hf (.step startE 8) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_svc_pre (p := (Ly).lab startE + Int64.ofNat (4 * 8)) hI cb4 rfl
      (startE8 (Ly).lab)
      (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 8 13) (by simp [startPhTab]))) (by decide)) hs.2
      (fun _ _ ⟨_, _, he⟩ => by rw [he, startS2_x8]; decide))
  · -- The call block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cc rfl Ret0.startCall_ok hR hal
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 9 Code.Start.startCall none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startCall_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 9 13) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_alloc_tcb`.
    obtain ⟨hR', hal'⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -192) hR hal
      (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    exact tcbW_wmono hW (tcbW_gen hI (fun _ => rfl) hrc.tcb hC0 hR' hal' (by show (-192 : Int) ≤ -192; omega)
      (by show (0 : Int) ≤ 0; omega) ⟨g, 0#64, c0⟩ rfl hg (tcbPh_ofPlaceOK h i hrt)
      (by rw [hpn]; exact ((Ly).words_mapped _ (Ly).pn_mem).1)
      (by rw [hpin]; exact PhRec.mapped_tcb h0)
      (fun m hm => by rw [hpn]; exact PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact PhRec.rtF_tcb (hFr m hm) h0) j)
  · -- `.sp2`'s block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI t0 (ofNat4_zero _) Ret0.startCall2_ok
      hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn
        (hf (.blk Code.Start.sp2L 0 Code.Start.startCall2 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startCall2_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph Code.Start.sp2L 0 12) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_thread_init`.
    obtain ⟨hR', hal'⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -256) hR hal
      (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    exact tiW_wmono hW (tiW_gen hI (fun _ => rfl) hrc.ti hC0 hR' hal' (by show (-256 : Int) ≤ -256; omega)
      (by show (0 : Int) ≤ 0; omega) ⟨g, pinA (Ly).lab + 0#64 + 8#64, k0, c0⟩ rfl hg (tiPh_ofPlaceOK h i hrt)
      (fun _ ha => PhRec.mapped_tcb (tcb_fld ha))
      (fun _ ha m hm => PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => PhRec.tcb_not_own (tcbSep h i) (tcb_fld ha))
      hsub hSMi hSMt hrc.take (takePh_ofPlaceOK h i hrt)
      (by rw [hlk]; exact ((Ly).words_mapped _ (Ly).lock_mem).1)
      (by rw [hfr]; exact ((Ly).words_mapped _ (Ly).freeN_mem).2.1)
      (by rw [hnx]; exact ((Ly).words_mapped _ (Ly).next_mem).1)
      (fun m hm => by rw [hlk]; exact PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnx]; exact PhRec.rtF_next (hFr m hm))
      hrS (rodata_stackPool_disjoint_ofPlaceOK h i) j)
  · -- `.sp3`'s block.
    exact blkW_wmono hW (blkW_post (dead := fun _ => false) (ra := 0) hI t2 (ofNat4_zero _) Ret0.startSw0_ok
      hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn
        (hf (.blk Code.Start.sp3L 0 Code.Start.startSw0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startSw0_noRet k hk r hr).elim) (fun _ _ _ => rfl) hsub hSM)
  · -- The `msr`.
    have hs := step_of_factOk hl (hf (.step Code.Start.sp3L 4) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_post (si := SI.msr .X10) (p := (Ly).lab Ret0.sp3L + Int64.ofNat (4 * 4))
      hI t3 rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hs.1 hs.2 hsub)

end Start

end Spike.Lib.A64.Rt
