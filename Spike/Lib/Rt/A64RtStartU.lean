/-
**`scc_rt_start`'s states inside `W`, for any placed output**
(`startAllUW_gen`): the obligations `StartAllUW` (`Spike/Lib/Rt/A64Segs.lean`)
of `scc_rt_start` at the record `RuntimeLayout.ofPlaceOK h i` of an output
passing `placeOK` whose program passes the decided phase table
(`rtPhOk … (rtPhTab none)`), at any write tail `Dt`: up to `.sp2` (`Sp0W`: the
entry's five nodes, the call block, `scc_rt_alloc_tcb` by `tcbW_gen`), from
`.sp2` to the switch (`Sp2W`: the block, `scc_rt_thread_init` by `tiW_gen`, the
block before the switch and the `msr`), and from the switch on as given
(`SwUW`).

- **The code**: the placed program's checks (`rtCodeIn_of_ok`): `startIn`,
  `startCallIn`, `startTailIn` and the callees'.
- **The phase facts**: `startPhTab`'s rows, and the callees' records
  (`tcbPh_ofPlaceOK`, `tiPh_ofPlaceOK`, `takePh_ofPlaceOK`); the nodes before
  `.sp3` are in phase `13` or `12`, before the take.
- **The words**: the record's, mapped (`words_mapped`) and unmapped under the
  frame condition (`rtF`); the TCB's owned at no phase (`tcbSep`); `.rodata`
  off the pool (`rodata_stackPool_disjoint_ofPlaceOK`), the take's premise,
  discharged here.
- **The write tail**: the generic lemmas give `SFacts` at the default write
  tail (no `write` before the switch); any `Dt` follows (`SFacts.dt_mono`,
  lifted through the obligations by `blkW_wmono` … `tiW_wmono`).
- **Oracle**: at `ret0`'s placed record (`Spike/Test/A64RtStartU.lean`).
-/
import Spike.Lib.Rt.A64RtPhRec
import Spike.Lib.Rt.A64RtCode
import Spike.Lib.A64StubFacts

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

namespace StartU

/-! ## A larger `W` -/

section WMono

variable {W W' : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F M : MachineData → Prop}

/-- A block obligation in a larger `W`. -/
theorem blkW_wmono (hW : ∀ s c, W s c → W' s c) {n : ND} {blk : List Directive}
    (h : BlkW W K exe endPc R F n blk) : BlkW W' K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJ k hk m hA' hD =>
    have h' := h s σ c he hn hd hpc hA hF hJ k hk m hA' hD
    ⟨hW _ _ h'.1, h'.2⟩

/-- A node obligation in a larger `W`. -/
theorem nodeW_wmono (hW : ∀ s c, W s c → W' s c) {n : ND} (h : NodeW W K exe endPc R F n) :
    NodeW W' K exe endPc R F n :=
  fun s c hA => ⟨hW _ _ (h s c hA).1, (h s c hA).2⟩

/-- `scc_rt_alloc_tcb`'s obligations in a larger `W`. -/
theorem tcbW_wmono (hW : ∀ s c, W s c → W' s c) {q : TcbG} {i : TN} (h : TcbW W K exe endPc R F q i) :
    TcbW W' K exe endPc R F q i := by
  cases i <;> dsimp only [TcbW] at h ⊢ <;> first | exact blkW_wmono hW h | exact nodeW_wmono hW h

/-- `scc_rt_stack_take`'s obligations in a larger `W`. -/
theorem takeW_wmono (hW : ∀ s c, W s c → W' s c) {q : TakeG} {i : TK} (h : TakeW W K exe endPc R F M q i) :
    TakeW W' K exe endPc R F M q i := by
  cases i <;> dsimp only [TakeW] at h ⊢ <;>
    first
    | exact blkW_wmono hW h
    | exact nodeW_wmono hW h
    | exact ⟨nodeW_wmono hW h.1, nodeW_wmono hW h.2⟩
    | exact fun s c hA => hW _ _ (h s c hA)

/-- `scc_rt_thread_init`'s obligations in a larger `W`. -/
theorem tiW_wmono (hW : ∀ s c, W s c → W' s c) {q : TiG} {i : TI} (h : TiW W K exe endPc R F M q i) :
    TiW W' K exe endPc R F M q i := by
  cases i <;> dsimp only [TiW] at h ⊢ <;>
    first
    | exact blkW_wmono hW h
    | exact nodeW_wmono hW h
    | exact fun g hg j => takeW_wmono hW (h g hg j)

end WMono

/-! ## `scc_rt_start`'s facts -/

theorem b0_noRet : noRetBlk Abort.b0 = true := by rfl
theorem startArgs_noRet : noRetBlk startArgs = true := by rfl
theorem startCall_noRet : noRetBlk Ret0.startCall = true := by rfl
theorem startCall2_noRet : noRetBlk Ret0.startCall2 = true := by rfl
theorem startSw0_noRet : noRetBlk Ret0.startSw0 = true := by rfl

/-- `rt_sigaction`'s number is in `x8` at `scc_rt_start`'s system call. -/
theorem startS2_x8 (lab : Label → Int64) (σ : Flow.AS) : (startS2 lab σ).regs.X8.toNat = 134 := by
  simp [startS2, startArgs_run]; rfl

/-- **A pc in a phase with bit 3 set** (before the take): no take there. -/
theorem noTk_of_ph {L : RuntimeLayout} {p : Int64} {v : Nat} (hp : PhRec.ph L p.toBitVec.toNat = v)
    (hv : v / 8 % 2 = 1) : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ PhRec.Tk L s := by
  intro s hs hT
  unfold PhRec.Tk at hT
  rw [hs, hp] at hT
  omega

/-- The arguments' pc. -/
theorem startE2 (lab : Label → Int64) : lab startE + 4 + 4 = lab startE + Int64.ofNat (4 * 2) := by
  rw [Int64.add_assoc]; rfl

/-- The system call's pc. -/
theorem startE8 (lab : Label → Int64) :
    lab startE + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = lab startE + Int64.ofNat (4 * 8) := by
  simp only [Int64.add_assoc]; rfl

/-- A callee's region below a 16-aligned region is one, 16-aligned. -/
theorem callee_facts {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) {kc lo' : Int}
    (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) (h16 : kc % 16 = 0) :
    (R.callee kc lo' 0).OK ∧ (R.callee kc lo' 0).base.toNat % 16 = 0 := by
  refine ⟨Region.callee_ok hR hlo hlo0 hkc (by omega), ?_⟩
  have hb := Region.callee_base (hi' := 0) hR hlo hlo0 hkc
  have : (((R.callee kc lo' 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **The first TCB's six fields** are words of the TCB. -/
theorem tcb_fld {L : RuntimeLayout} {a : BitVec 64} (ha : a ∈ Ti.tiAddrs (pinA L.lab + 0#64 + 8#64)) :
    ∃ j < 7, a = L.pinA + BitVec.ofNat 64 (8 * j) := by
  rw [show pinA L.lab = L.pinA from L.lab_pin, BitVec.add_zero] at ha
  simp only [Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨2, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨3, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨4, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨5, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨6, by decide, by rw [BitVec.add_assoc]; rfl⟩

end StartU

/-! ## The obligations -/

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option maxHeartbeats 1600000 in
open StartU PhRecOf PhOfTab in
/-- **`scc_rt_start`'s states are inside `SFacts … Dt`** at the record of an
output passing `placeOK` (`h`, at the immediates `i`) whose program passes
the table (`hrt`), at any write tail `Dt`, in any region holding its frame and
its callees' below (`hR` … `hhi`), with the source control `c0` (`hC0`, its
facts), the frame condition giving the runtime's words unloaded (`hFr`), the
first TCB (`hn0`) and the first stack `rS` (`hrS`) in the pool (`hsub`) kept
by the writes of the three regions (`hSM`, `hSMi`, `hSMt`), and the switch's
and `scc_rt_main`'s obligations (`hs3`). -/
theorem startAllUW_gen
    (hrt : Scc.Cert.Rt.A64.rtPhOk (Ly).Λ.code.lo o.prog (Ly).Λ (rtPhTab none) = true)
    {p : Prog} {lbl : Lbl} {ms : MemSide isaLSE2} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {n0 k0 : BitVec 64} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS)) (hSMi : FStable (R.callee Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hs3 : SwUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R (fun m => F m ∧ StackM rS m) ms rS
      (pinA (Ly).lab + n0 + 8#64) (stacksA (Ly).lab + k0 + 16384#64) c0 L mc D ZU Post) :
    StartAllUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R F ms rS n0 k0 c0 L mc D ZU Post := by
  subst hn0
  have hI := PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h)
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
