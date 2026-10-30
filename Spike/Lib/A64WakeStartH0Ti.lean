/-
**`wake_start_wc_place`'s `htiW` at a placed output** (AArch64): `StartTi.startTi_WS` at the runtime's layout
`Ly := RuntimeLayout.ofPlaceW hpw i`, the callee's region
`(entryR E).callee oI.sp (-256) 0` below the entry stack, `F := FWN`, the
first stack `Rt.rS0 Ly`, wake's arena `WakeOD.arW` and clone phase
`WakeOD.ClW`, the first TCB.

Discharged here: the callee's region (`callee_facts`), its frames off the
pool (`bandI_entry`, the entry stack clear of the pool), the stack's
stability (`stackM_rS0`), the TCB's, lock's and next offset's words off
the arena and its counter (`offW_arW`: runtime words are `.data`/pinned
words, the counter not one of them), the labels and the take site.

`X0W` across `scc_rt_thread_init … scc_rt_stack_release` (`x0W_ti`): off
the take site below the clone; at the site the range `rS0 = r0Of`, not
yet in private memory from the site frame `Pz rS0` (`Pz.pz_not_stackM`).
The frame `Pz rS0` is kept by the entry region's frames
(`pz_fstable_entry`: the pool, so `rS0`, is clear of the entry stack).

The words' separation `hs` at `ntA` (`wsep_W`, from A13's data part).

Left: `hro`, `hC0`, `hc0`, `hpl0`.

- `offW_arW`: a runtime word is off `arW`'s cells and counter;
- `bandI_entry`: `[-256, 0]` of the callee below the entry `sp` is off the pool;
- `pz_fstable_entry`: `Pz rS0` is kept by the entry region's frames;
- `htiW_place`: `htiW` in `wake_start_wc_place`'s shape.
-/
import Spike.Lib.A64WakeStartH0
import Spike.Lib.A64WakeStartTiW
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakePz

namespace Spike.Lib.A64.WakePh.StartH0Ti

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP)
open Spike.Lib (Arena FragS Region)
open Spike.Lib.A64.WakePh (lo)

/-- `x - k` as `x + ofInt (-k)`, `k ≤ x`. -/
private theorem toNat_addNeg {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) :
    (x + BitVec.ofInt 64 (-(k : Int))).toNat = x.toNat - k := by
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofInt]
  have : ((-(k : Int)) % (2 ^ 64 : Nat) : Int).toNat = if k = 0 then 0 else 2 ^ 64 - k := by split <;> omega
  rw [this]; split <;> omega

/-- **The callee's frame `[-256, 0]` below the entry `sp` is off the pool**
(the pool is clear of the entry stack, `pool_clear`). -/
theorem bandI_entry {L : RuntimeLayout} {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    Spike.Lib.A64.WakePh.StartTi.BandI L ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (-256) := by
  intro k h1 h2
  have hb := Spike.Lib.A64.Rt.entryR_base hE
  have := Spike.Lib.A64.Rt.entry_sp hE
  have hd := Spike.Lib.A64.Rt.pool_clear L hE.1
  have hs := Spike.Lib.A64.Rt.entryR_sub hE
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  have hx : ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0).addr k =
      (entryR E).base + BitVec.ofInt 64 (-((48 - k).toNat : Int)) := by
    simp only [Region.callee, Region.addr, BitVec.add_assoc, ← BitVec.ofInt_add]
    congr 2; show (-48 : Int) + k = _; omega
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hd hs
  rw [hx, toNat_addNeg (by omega), hb]
  omega

open Spike.Lib.A64.WakePh.WcW (cv freeLabs lab_cv clone_inCv) in
/-- **`X0W` in `scc_rt_thread_init … scc_rt_stack_release`**: off the take
site, below the clone (`startTi_WS`'s `hX0`); at the site, from the site's
range `rS0` and its first word unmapped (`Pz`, `startTi_WS`'s `hXs`). -/
private theorem x0W_ti {L : RuntimeLayout} {ax : Int64}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    (∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → Spike.Lib.A64.WakeWf.X0W L ax s) ∧
    (∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab →
      Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1 → Spike.Lib.A64.WakeWf.X0W L ax s) := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cv l by
    have := List.all_eq_true.mp freeLabs l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cv hlab this.1 this.2
  have hc := clone_inCv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc.1.1
  have ey : cv ".L21_wc_main.sp6" = y := by simp [cv, hy]
  have e : Spike.Lib.A64.Flow.WakeWc.clonePc L = y + 52 := by
    show (L.lab (".L21_wc_main" ++ ".sp6") + Int64.ofNat (4 * 13)).toBitVec.toNat = y + 52
    rw [show (".L21_wc_main" ++ ".sp6" : String) = ".L21_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 52).toNat = y + 52
    have := hc.1.2; rw [ey] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : decide (cv "scc_rt_stack_release" ≤ cv ".L21_wc_main.sp6") = true := by
    unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  simp only [decide_eq_true_eq] at hd
  have hs : (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat < cv "scc_rt_stack_release" := by
    have hd2 : decide (cv Spike.Lib.A64.Flow.Ret0.StackTake.siteL < cv "scc_rt_stack_release") = true := by
      unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
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

/-- **`Pz rS0` is kept by the entry region's frames**: the region lies in
the entry stack (`entryR_sub`), clear of the pool (`pool_clear`, from the
entry's `E.clear`), which holds `rS0` (`rS0_sub`); so `rS0`'s first word is
below the region or at or above its top. -/
theorem pz_fstable_entry {L : RuntimeLayout} {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    Spike.Lib.A64.Flow.FStable (entryR E) (Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.rS0 L)) := by
  intro m m' h hd
  have hb := Spike.Lib.A64.Rt.entryR_base hE
  have hd0 := Spike.Lib.A64.Rt.pool_clear L hE.1
  have hs := Spike.Lib.A64.Rt.entryR_sub hE
  have hsub := L.stacks_sub
  have hf := L.pool_fit
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  have hr : (Spike.Lib.A64.Rt.rS0 L).lo = L.stacksA.toNat := by
    show (L.stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hd0 hs hsub
  have hn : (BitVec.ofNat 64 L.stacksA.toNat).toNat = L.stacksA.toNat := by
    rw [BitVec.toNat_ofNat]; omega
  unfold Spike.Lib.A64Consumer.Pz at h ⊢
  rw [hr] at h ⊢
  rw [hd _ (by rw [hn]; omega) (by
    rw [hn, hb]
    show (L.stacksA.toNat : Int) + 8 ≤ (E.sp : Int) + -65536 ∨ (E.sp : Int) + 0 ≤ L.stacksA.toNat
    omega)]
  exact h

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

/-- **A runtime word is off `arW`'s cells and its counter**: its bytes lie
in `.data` or the pinned region, both clear of the heap; the counter is
separate from it (`ctrSep_of_rtWordsOk`). -/
theorem offW_arW : ∀ w ∈ (Ly).rtWords, ¬ ((AR).heap ≤ w.toNat ∧ w.toNat < (AR).heap + 16 * (AR).cells) ∧
    (⟨w, 8⟩ : Loc) ≠ (AR).ctrLoc := fun w hw => by
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  obtain ⟨hh, hc, hu⟩ := Spike.Lib.WakeOD.har_arW hpw i
  have hm := ((Ly).words_mapped w hw).2.2 0 (by decide)
  obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (show (Ly).Λ.WF from hwf).disjoint
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hsep : Scc.Cert.Rt.A64.WordSep w (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
    Scc.Cert.Rt.A64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceW.rtWordsOk_link_of_placeW i hpw) w hw
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint, Scc.Cert.Rt.A64.WordSep] at hm hdh hph hsep
  refine ⟨by rw [hh, hc]; omega, fun he => ?_⟩
  have := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Arena.ctrLoc, hu] at this
  omega

/-- A word of the first TCB is a runtime word. -/
private theorem tcb_rtWord {b : BitVec 64} (hb : b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (pinA (Ly).lab + 0#64 + 8#64)) :
    b ∈ (Ly).rtWords := by
  obtain ⟨j, hj, rfl⟩ := Spike.Lib.A64.Rt.StartU.tcb_fld hb
  rcases j with _ | j
  · simp [Spike.Lib.A64.Rt.rtWordsOf]
  · simp only [Spike.Lib.A64.Rt.rtWordsOf, List.mem_append, List.mem_map, List.mem_range]
    exact .inr ⟨j, by omega, rfl⟩

set_option maxHeartbeats 800000 in
/-- **`wake_start_wc_place`'s `htiW`** at `arW`/`ClW`: `startTi_WS` with the
region, stack, word and label premises discharged, at the site frame
`Pz rS0` (`x0W_ti`'s site case). -/
theorem htiW_place {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ) {p : Prog} {Dt : State → Prop}
    {Ctx : FragS isaLSE2} {lbl lbl' : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64}
    (hp : o.prog = wakeProg) (hlo : (Ly).Λ.code.lo = lo)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.A64Consumer.CFacts (Ly).Λ lbl' c0) :
    ∀ g, g.ra = ((Ly).lab Spike.Lib.A64.Flow.Ret0.sp3L).toBitVec → ∀ j,
      Spike.Lib.A64.Flow.Ret0.TiW (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (AR) p Dt (Spike.Lib.WakeOD.ClW hpw i) Ctx lbl lsize frM
        (Spike.Lib.A64.WakeWf.X0W (Ly) ax))
        (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0)
        FWN (Spike.Lib.A64.Flow.Ret0.StackM RS) ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ j
        (Spike.Lib.A64Consumer.Pz RS) := by
  intro g hra
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hSM := Spike.Lib.LowerA64.stackM_rS0 (Ly) hE
  obtain ⟨hR, hal⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -256)
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -48 + -256; decide)
    (by decide) (by show (-48 : Int) < 0; decide) (by decide)
  exact Spike.Lib.A64.WakePh.StartTi.startTi_WS hp hlo hlab (Spike.Lib.PlaceW.site_ofPlaceW hpw i)
    (fun _ h => h.2) hc0 hpl0 (x0W_ti hlab hax).1 (bandI_entry hE) hΛ
    (Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hpw i hA13) hro hC0 hR hal (show (-256 : Int) ≤ -256 by decide) (show (0 : Int) ≤ 0 by decide) (fun _ h => h.2)
    ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ rfl rfl hra (by rw [Spike.Lib.A64.Rt.stacksA_lab0])
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) hSM.2.1 hSM.2.2 (fun b hb => offW_arW hpw i b (tcb_rtWord hpw i hb))
    (offW_arW hpw i _ (Ly).lock_mem) (offW_arW hpw i _ (Ly).next_mem)
    (fun s hp hr _ hz => (x0W_ti hlab hax).2 s hp
      (hr.trans (by rw [Spike.Lib.A64.Rt.Ti2.r0Of, Spike.Lib.A64.Rt.stacksA_lab0]))
      (by rw [Spike.Lib.A64.Rt.Ti2.r0Of, Spike.Lib.A64.Rt.stacksA_lab0]; exact hz))

end Spike.Lib.A64.WakePh.StartH0Ti

/-- info: 'Spike.Lib.A64.WakePh.StartH0Ti.htiW_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0Ti.htiW_place

/-- info: 'Spike.Lib.A64.WakePh.StartH0Ti.pz_fstable_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0Ti.pz_fstable_entry
