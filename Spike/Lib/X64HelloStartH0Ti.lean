/-
**`hello_start_wc_place`'s `htiW` at a placed output** (hello.w, x86-64;
twin of `Spike/Lib/A64HelloStartH0Ti.lean`, hello's copy of wake's x86-64
`X64WakeRootTi`): hello's `StartTi.startTi_WSPH` at the runtime's layout
`Ly := RuntimeLayout.ofPlaceWX hpw i` (`o.prog = helloCells`), the callee's
region `((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8` below
the entry stack, every frame `F'` inside `FWN`, the first stack `Rt.rS0 Ly`,
the arena `WakeOD.arW`, hello's clone phase `HelloPh.ClH`, the first TCB.

Reused from wake as is (layout generic, no hello copy): the callee's frames
off the pool (`RootTi.bandI_entry`), the first stack kept by the callees'
regions (`RootTi.stackM_entry`), the TCB's words as runtime words
(`RootTi.tcb_rtWord`), the words' separation (`StartPlaceLy.wsep_W`), a
runtime word off the arena (`CalWf.off_of`).

Hello's copies (they read hello's labels):

- `x0WH_ti`: `X0WH` across `scc_rt_thread_init … scc_rt_stack_release`, off
  the take site below hello's clone (`.Lwc_main.x25 + 94`); at the site the
  range `rS0`, not yet in private memory (`Pz.pz_not_stackM`).
- `tcb_rtWordH`: a word of the first TCB is a runtime word.
- `htiWH_place`: `htiW` in `hello_start_wc_place`'s shape.

Left: `hro`, `hC0`, `hc0`, `hpl0`, `hA13` (as at wake).

## Differences from the AArch64 version

- AArch64's `TiW … P` is x86-64's `Rt.TiWAtP … x8L P` (`StartTi.startTi_WSPH`;
  hello's `scc_rt_thread_init` returns to `.x8`), its call returning to
  `Ret0.x1L` (AArch64's `sp3L`). As on wake's x86-64 `RootTi.hti_root`, the
  statement holds for every frame `F'` inside `FWN` kept by the entry callee's
  region and by `K` (`MainGlue`'s `hti` shape), and the region is the entry's
  callee at `-8` (the return-address word) and then `thread_init`'s at
  `-48 - 0` (AArch64's `(entryR E).callee oI.sp (-256) 0`).
- `x0WH_ti`'s site case is stated at `rS0 Ly` and any frame `F` (`startTi_WSPH`'s
  `hXs`); AArch64's at `r0Of` (`RootP.r0Of_rS0` relates them). The clone is the
  `syscall` at `.Lwc_main.x25 + 94` (AArch64's `svc` at `.L22_wc_main.sp6 + 100`).
- The arena's offsets come from `CalWf.off_of` and `ctrSep_of_rtWordsOk` at
  `PlaceWX` (AArch64's `StartH0Ti.offW_arW`).
-/
import Spike.Lib.X64HelloStartTiP
import Spike.Lib.X64HelloStartGlue
import Spike.Lib.X64HelloClH
import Spike.Lib.X64WakeRootTi
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64WakeWfCalOff
import Spike.Lib.X64SiteOfPlaceW

namespace Spike.Lib.X64.HelloPh.StartH0Ti

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF rS0)
open Spike.Lib.X64Consumer (Lbl Lsize Pz)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.Flow.Ret0 (pinA)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS Region PlaceWX)
open Spike.Lib.X64.HelloPh (lo)

open Spike.Lib.X64.HelloPh.WcW (cvH freeLabsH lab_cvH clone_inCvH) in
/-- **`X0WH` in `scc_rt_thread_init … scc_rt_stack_release`**: off the
take site, below hello's clone (`startTi_WSPH`'s `hX0`); at the site, from
the site's range `rS0` and its first word unmapped (`Pz`, `startTi_WSPH`'s
`hXs` at any frame `F`). -/
theorem x0WH_ti {L : RuntimeLayout} {ax : Int64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    (∀ s, Spike.Lib.X64.WakePh.inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0WH L ax s) ∧
    (∀ (F : MachineData → Prop) s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS0 L → F s.st.1 → Pz (rS0 L) s.st.1 → X0WH L ax s) := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cvH l by
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cvH hlab this.1 this.2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, -⟩ := hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
  have ey : cvH ".Lwc_main.x25" = y := by simp [cvH, hy]
  have e : Spike.Lib.X64HelloPreA.clonePcH L = y + 94 := by
    rw [ey] at hb
    show (L.lab ".Lwc_main.x25" + 94).toBitVec.toNat = y + 94
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 94).toNat = y + 94
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : decide (cvH "scc_rt_stack_release" ≤ cvH ".Lwc_main.x25") = true := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  simp only [decide_eq_true_eq] at hd
  rw [ey] at hd
  have hst : (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat < cvH "scc_rt_stack_release" := by
    have hd2 : decide (cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL < cvH "scc_rt_stack_release") = true := by
      unfold cvH; rw [← codeT_eq]; decide +kernel
    rw [hl (by simp)]; exact of_decide_eq_true hd2
  have hal : (Spike.Lib.X64.Rt.Ti2.r0Of L.lab).lo % 8 = 0 := by
    rw [(Spike.Lib.X64.Rt.Ti2.r0Of_eq L.lab).1, L.lab_stacks]; have := L.stacks_al; omega
  refine ⟨fun s h hne => ⟨?_, fun he => absurd (he.trans hax) hne⟩,
    fun _ s hp hr _ hz => ⟨?_, fun _ => ⟨?_, ?_⟩⟩⟩
  · unfold Spike.Lib.X64.WakePh.inPc at h
    rw [hl (by simp), hl (by simp)] at h
    rw [e]; omega
  · rw [e, hp]; omega
  · rw [hr, Spike.Lib.X64.WakePh.RootP.r0Of_rS0]
  · have hz' : Pz (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s.st.1 := by
      rw [Spike.Lib.X64.WakePh.RootP.r0Of_rS0]; exact hz
    exact Spike.Lib.X64.WakePh.Pz.pz_not_stackM hal
      (by rw [(Spike.Lib.X64.Rt.Ti2.r0Of_eq L.lab).2]; decide) hz'

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS" => rS0 (Ly)

/-- A word of the first TCB is a runtime word (`RootTi.tcb_rtWord` at `Ly`). -/
private theorem tcb_rtWordH {b : BitVec 64}
    (hb : b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (pinA (Ly).lab + 0#64 + 8#64)) : b ∈ (Ly).rtWords :=
  Spike.Lib.X64.WakePh.RootTi.tcb_rtWord hb

set_option maxHeartbeats 800000 in
/-- **`hello_start_wc_place`'s `htiW`** at `arW`/`ClH`: `startTi_WSPH` with
the region, stack, word and label premises discharged, at the site frame
`Pz rS0` (`x0WH_ti`'s site case), for every frame `F'` inside `FWN`. -/
theorem htiWH_place {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ) {p : Prog} {Dt : State → Prop}
    {Ctx : FragS isa} {lbl lbl' : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64}
    (hp : o.prog = helloCells) (hlo : (Ly).Λ.code.lo = lo)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.X64Consumer.CFacts (Ly).Λ lbl' c0) :
    ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable ((entryR E).callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K (Ly) RS) F' → (∀ m, F' m → FWN m) →
      ∀ g, g.ra = ((Ly).lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ j,
      Spike.Lib.X64.Rt.TiWAtP
        (WSH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (AR) p Dt (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx lbl lsize
          frM (X0WH (Ly) ax))
        (Spike.Lib.X64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc
        (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM RS)
        ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ Spike.Lib.X64.Rt.x8L (Pz RS) j := by
  intro F' _ _ hF' g hra
  have hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hoff : ∀ w ∈ (Ly).rtWords, ¬ ((AR).heap ≤ w.toNat ∧ w.toNat < (AR).heap + 16 * (AR).cells) ∧
      (⟨w, 8⟩ : Loc) ≠ (AR).ctrLoc := fun w hw =>
    Spike.Lib.X64.WakePh.CalWf.off_of hpw i (by simpa using ((Ly).words_mapped _ hw).2.2 0 (by decide))
      (Spike.Lib.X64.WakePh.CalWf.ne_of_sep
        (Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hpw) _ hw))
  have hR := Spike.Lib.X64.Rt.entryR_ok hE
  have hR1 := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR
    (by show (-65536 : Int) ≤ _; decide) (by decide) (by show (-8 : Int) < 0; decide)
    (by show (-8 : Int) + 8 ≤ 0; decide)
  have hR2 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR1
    (by show (-296 : Int) ≤ _; decide) (by decide) (by show (-48 - 0 : Int) < 8; decide)
    (by show (-48 - 0 : Int) + 8 ≤ 8; decide)
  have hSM := Spike.Lib.X64.WakePh.RootTi.stackM_entry hE
  have hX := x0WH_ti hlab hax
  exact Spike.Lib.X64.HelloPh.StartTi.startTi_WSPH hp hlo hlab (Spike.Lib.PlaceWX.site_ofPlaceWX hpw i)
    (Spike.Lib.X64.HelloPh.ClH.cl) hc0 hpl0 hX.1 (Spike.Lib.X64.WakePh.RootTi.bandI_entry hE) hΛ
    (Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw i hA13) hro hC0 hR2 (show (-248 : Int) ≤ -248 by decide)
    (show (8 : Int) ≤ 8 by decide) (fun m h => (hF' m h).2)
    ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ rfl rfl hra
    (by show rS0 (Ly) = _; rw [Spike.Lib.X64.Rt.stacksA_lab0]) (Spike.Lib.X64.Rt.rS0_sub (Ly)) hSM.1 hSM.2
    (fun b hb => hoff b (tcb_rtWordH hpw i hb)) (hoff _ (Ly).lock_mem) (hoff _ (Ly).next_mem) (hX.2 F')

end Spike.Lib.X64.HelloPh.StartH0Ti

/-- info: 'Spike.Lib.X64.HelloPh.StartH0Ti.x0WH_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0Ti.x0WH_ti

/--
info: 'Spike.Lib.X64.HelloPh.StartH0Ti.htiWH_place' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0Ti.htiWH_place
