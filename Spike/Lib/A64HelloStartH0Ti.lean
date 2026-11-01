/-
**`hello_start_wc_place`'s `htiW` at a placed output** (hello.w, AArch64;
twin of `A64WakeStartH0Ti`): hello's
`StartTi.startTi_WSH` at the runtime's layout
`Ly := RuntimeLayout.ofPlaceW hpw i` (`o.prog = helloProg`), the callee's
region `(entryR E).callee oI.sp (-256) 0` below the entry stack,
`F := FWN`, the first stack `Rt.rS0 Ly`, the arena `WakeOD.arW` (defined
for any `PlaceW` output) and hello's clone phase `HelloPh.ClH`, the first
TCB.

Reused from wake as is (layout generic, no hello copy): the callee's frames
off the pool (`StartH0Ti.bandI_entry`), the site frame kept by the entry
region's frames (`StartH0Ti.pz_fstable_entry`), the runtime's words off the
arena and its counter (`StartH0Ti.offW_arW`), the words' separation
(`StartPlaceLy.wsep_W`).

Hello's copies (they read hello's labels):

- `x0WH_ti`: `X0WH` across `scc_rt_thread_init … scc_rt_stack_release`, off
  the take site below hello's clone (`.L22_wc_main.sp6 + 100`); at the site
  the range `rS0 = r0Of`, not yet in private memory (`Pz.pz_not_stackM`).
- `htiWH_place`: `htiW` in `hello_start_wc_place`'s shape.

Left: `hro`, `hC0`, `hc0`, `hpl0`, `hA13` (as at wake).
-/
import Spike.Lib.A64HelloStartTiW
import Spike.Lib.A64HelloStartGlue
import Spike.Lib.A64HelloClH
import Spike.Lib.A64WakeStartH0Ti

namespace Spike.Lib.A64.HelloPh.StartH0Ti

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS Region)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakePh.StartH0Ti (bandI_entry offW_arW)

open Spike.Lib.A64.HelloPh.WcW (cvH freeLabsH lab_cvH clone_inCvH) in
/-- **`X0WH` in `scc_rt_thread_init … scc_rt_stack_release`**: off the
take site, below hello's clone (`startTi_WSH`'s `hX0`); at the site, from
the site's range `rS0` and its first word unmapped (`Pz`, `startTi_WSH`'s
`hXs`). -/
theorem x0WH_ti {L : RuntimeLayout} {ax : Int64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    (∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0WH L ax s) ∧
    (∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab →
      Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1 → X0WH L ax s) := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cvH l by
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cvH hlab this.1 this.2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc.1.1
  have ey : cvH ".L22_wc_main.sp6" = y := by simp [cvH, hy]
  have e : Spike.Lib.HelloPreA.clonePcH L = y + 100 := by
    show (L.lab (".L22_wc_main" ++ ".sp6") + Int64.ofNat (4 * 25)).toBitVec.toNat = y + 100
    rw [show (".L22_wc_main" ++ ".sp6" : String) = ".L22_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 100).toNat = y + 100
    have := hc.1.2; rw [ey] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : decide (cvH "scc_rt_stack_release" ≤ cvH ".L22_wc_main.sp6") = true := by
    unfold cvH; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  simp only [decide_eq_true_eq] at hd
  have hs : (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat < cvH "scc_rt_stack_release" := by
    have hd2 : decide (cvH Spike.Lib.A64.Flow.Ret0.StackTake.siteL < cvH "scc_rt_stack_release") = true := by
      unfold cvH; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
    rw [hl (by simp)]; exact of_decide_eq_true hd2
  have hr0 : (Spike.Lib.A64.Rt.Ti2.r0Of L.lab).lo = L.stacksA.toNat := by
    show (Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels L.exe).label + 0#64).toNat = _
    rw [L.lab_stacks, BitVec.add_zero]
  have hal := L.stacks_al
  refine ⟨fun s h hne => ⟨?_, fun he => absurd (he.trans hax) hne⟩, fun s hp hr hu => ⟨?_, fun _ => ⟨hr,
    Spike.Lib.A64.WakePh.Pz.pz_not_stackM (by rw [hr0]; omega) (by exact (by decide : 8 ≤ 16384)) hu⟩⟩⟩
  · unfold Spike.Lib.A64.WakePh.inPc at h
    rw [hl (by simp), hl (by simp)] at h
    rw [e]; omega
  · rw [e, hp]; omega

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

/-- A word of the first TCB is a runtime word. -/
private theorem tcb_rtWordH {b : BitVec 64}
    (hb : b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (pinA (Ly).lab + 0#64 + 8#64)) : b ∈ (Ly).rtWords := by
  obtain ⟨j, hj, rfl⟩ := Spike.Lib.A64.Rt.StartU.tcb_fld hb
  rcases j with _ | j
  · simp [Spike.Lib.A64.Rt.rtWordsOf]
  · simp only [Spike.Lib.A64.Rt.rtWordsOf, List.mem_append, List.mem_map, List.mem_range]
    exact .inr ⟨j, by omega, rfl⟩

set_option maxHeartbeats 800000 in
/-- **`hello_start_wc_place`'s `htiW`** at `arW`/`ClH`: `startTi_WSH` with
the region, stack, word and label premises discharged, at the site frame
`Pz rS0` (`x0WH_ti`'s site case). -/
theorem htiWH_place {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ) {p : Prog} {Dt : State → Prop}
    {Ctx : FragS isaLSE2} {lbl lbl' : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64}
    (hp : o.prog = SccCode.helloProg) (hlo : (Ly).Λ.code.lo = lo)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.A64Consumer.CFacts (Ly).Λ lbl' c0) :
    ∀ g, g.ra = ((Ly).lab Spike.Lib.A64.Flow.Ret0.sp3L).toBitVec → ∀ j,
      Spike.Lib.A64.Flow.Ret0.TiW
        (WSH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (AR) p Dt (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx lbl lsize
          frM (X0WH (Ly) ax))
        (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0)
        FWN (Spike.Lib.A64.Flow.Ret0.StackM RS) ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ j
        (Spike.Lib.A64Consumer.Pz RS) := by
  intro g hra
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hSM := Spike.Lib.LowerA64.stackM_rS0 (Ly) hE
  obtain ⟨hR, hal⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -256)
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -48 + -256; decide)
    (by decide) (by show (-48 : Int) < 0; decide) (by decide)
  exact Spike.Lib.A64.HelloPh.StartTi.startTi_WSH hp hlo hlab (Spike.Lib.PlaceW.site_ofPlaceW hpw i)
    (fun _ h => h.2) hc0 hpl0 (x0WH_ti hlab hax).1 (bandI_entry hE) hΛ
    (Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hpw i hA13) hro hC0 hR hal (show (-256 : Int) ≤ -256 by decide)
    (show (0 : Int) ≤ 0 by decide) (fun _ h => h.2)
    ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ rfl rfl hra (by rw [Spike.Lib.A64.Rt.stacksA_lab0])
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) hSM.2.1 hSM.2.2 (fun b hb => offW_arW hpw i b (tcb_rtWordH hpw i hb))
    (offW_arW hpw i _ (Ly).lock_mem) (offW_arW hpw i _ (Ly).next_mem)
    (fun s hp hr _ hz => (x0WH_ti hlab hax).2 s hp
      (hr.trans (by rw [Spike.Lib.A64.Rt.Ti2.r0Of, Spike.Lib.A64.Rt.stacksA_lab0]))
      (by rw [Spike.Lib.A64.Rt.Ti2.r0Of, Spike.Lib.A64.Rt.stacksA_lab0]; exact hz))

end Spike.Lib.A64.HelloPh.StartH0Ti

/-- info: 'Spike.Lib.A64.HelloPh.StartH0Ti.x0WH_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0Ti.x0WH_ti

/-- info: 'Spike.Lib.A64.HelloPh.StartH0Ti.htiWH_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0Ti.htiWH_place
