/-
**`scc_rt_main` after a setup block inside the runtime's world `RtM`**
(x86-64): its own states (`MainSW`, `Spike/Lib/Rt/X64MainS.lean`), the
prologue's, the setup call's, the marshalling block's and the `exit_group`
tail's, each node's obligation inside `RtM` (`Spike/Lib/LowerX64/RtStartX.lean`):
the write abort's phase kept and no write to the arena.

- `MainPhS`: `scc_rt_main`'s phase facts at a setup code `sc`, the rows of
  `mainPhTabS sc`; `mainPhS_of_tab` from a checked table holding them,
  `mainPhS_of_placeOKAt` at an output passing `placeOK` with a setup block
  (A11, some `sw < 6`);
- `blkW_rtM`: `blkW_rtMG` for a block without `ret` nor a branch to the
  abort, its targets positioned off the write abort;
- `marshal_facts`, `setupMC_Z`, `setupMC_k`: the marshalling block's
  labels and ends, and the frame's sizes, at each `sw < 6`;
- `mainSW_rtM`: `MainSW` inside `RtM` at `setupMC sw`, for any program
  with its code (`mainSIn`) and the runtime's, its phase facts, the
  growth path, the setup block and the user function positioned off the
  write abort (`hgrow`, `hset`, `hfn`), in any region holding its frame
  and a return address.
-/
import Spike.Lib.LowerX64.RtStartXOf
import Spike.Lib.LowerX64.SetupOfPlaceOK
import Spike.Lib.Rt.X64MainS
import Spike.Lib.Rt.X64RtPhRec

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND classify cellOff okBlk okBlk_callB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xHead xLea xCmp xFr xExit xHead_ok xLea_ok xCmp_ok xFr_ok
  xExit_ok prologueIn exitIn)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout SetupCode setupMC mainPhTabS rtCodeOkS setupFr marshal MainSW
  mainSIn okBlk_marshal)
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet callB_noRet xExit_noRet)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-! ## The phase facts -/

/-- **`scc_rt_main`'s phase facts at the setup code `sc`** at labels `lab`,
phase index `ph`, off-site pcs `okPc` (the rows of `mainPhTabS sc`): the
prologue's blocks, the setup call's, the marshalling block's and the tail's
at their pcs, no dead target; the limit's load and the `syscall` off the
sites and in their next pc's phase. -/
structure MainPhS (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (sc : SetupCode) : Prop where
  hd : blkPh okPc ph (fun _ => false) lab (lab "scc_rt_main" + Int64.ofNat 0) 0 xHead = true
  lea : blkPh okPc ph (fun _ => false) lab (lab sc.sc + Int64.ofNat 0) 0 (xLea sc.Z 5) = true
  ld : okPc (lab sc.sc + Int64.ofNat 5).toBitVec.toNat = true ∧
    ph (lab sc.sc + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat = ph (lab sc.sc + Int64.ofNat 5).toBitVec.toNat
  cmp : blkPh okPc ph (fun _ => false) lab (lab sc.sc + Int64.ofNat 14) 0 (xCmp sc.grow 3 2) = true
  fr : blkPh okPc ph (fun _ => false) lab (lab sc.sc + Int64.ofNat 19) 0 (setupFr sc) = true
  call0 : blkPh okPc ph (fun _ => false) lab (lab sc.e0 + Int64.ofNat 0) 0 (Spike.Lib.X64.callB sc.setup) = true
  sp0 : blkPh okPc ph (fun _ => false) lab (lab sc.sp0 + Int64.ofNat 0) 0 (marshal sc.sw sc.fn) = true
  ex : blkPh okPc ph (fun _ => false) lab (lab sc.sp1 + Int64.ofNat 0) 0 (xExit sc.k 4 4 5) = true
  svc : okPc (lab sc.sp1 + Int64.ofNat 13).toBitVec.toNat = true ∧
    ph (lab sc.sp1 + Int64.ofNat 13 + Int64.ofNat 2).toBitVec.toNat = ph (lab sc.sp1 + Int64.ofNat 13).toBitVec.toNat

section Tab

open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.PhRec (ph okPc)
open Scc.Sem.X64 (codeLabel)

variable (L : RuntimeLayout)
  (hlab : ∀ l a, codeLabel L.Λ.code.lo L.prog l = some a → L.lab l = Int64.ofNat a)
  {tab : List Scc.Cert.Rt.X64.PhFact} (hrt : Scc.Cert.Rt.X64.rtPhOk L.Λ.code.lo L.prog L.Λ tab = true)

include hlab hrt

/-- **`scc_rt_main`'s phase facts at `sc`** of a checked table holding
`mainPhTabS sc`. -/
theorem mainPhS_of_tab {sc : SetupCode} (hsub : ∀ f ∈ mainPhTabS sc, f ∈ tab) :
    MainPhS (okPc L) (ph L) L.lab sc := by
  have hf : ∀ f ∈ mainPhTabS sc, _ := fun f hf => Scc.Cert.Rt.X64.factOk_of_rtPhOk hrt (hsub f hf)
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel L.Λ.code.lo L.prog) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = L.lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  exact {
    hd := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    lea := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    ld := step_of_factOk hlab (hf (.step sc.sc 5 9) (by simp [mainPhTabS]))
    cmp := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    fr := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    call0 := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    sp0 := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    ex := blkPh_of_factOk hlab hr hn (hf _ (by simp [mainPhTabS]))
    svc := step_of_factOk hlab (hf (.step sc.sp1 13 2) (by simp [mainPhTabS])) }

end Tab

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **`scc_rt_main`'s code and phase facts after a setup block** at an
output passing `placeOK` whose tail has one (A11): some `sw < 6` with the
runtime's code at `setupMC sw` and `MainPhS` there. -/
theorem mainPhS_of_placeOKAt (hs : o.place.tail = .setup) :
    ∃ sw < 6, rtCodeOkS o.prog (setupMC sw) = true ∧
      MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw) := by
  obtain ⟨sw, hsw, hc, hp⟩ := setupIn_of_placeOKAt h hs
  exact ⟨sw, hsw, hc, mainPhS_of_tab (Ly) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i) hp fun _ hf => hf⟩

end Place

/-! ## The setup code's facts -/

/-- **The marshalling block at each `sw < 6`**: no `ret`, its one label
the user function, its last instruction (the call) not falling through. -/
theorem marshal_facts : ∀ sw < 6, noRetBlk (marshal sw "wc_main") = true ∧
    blkLabs (marshal sw "wc_main") = ["wc_main"] ∧ lastFalls (marshal sw "wc_main") = false := by
  decide

/-- The frame's size at `sw` words. -/
theorem setupMC_Z : ∀ sw < 6, (setupMC sw).Z.toInt = (((8 * (sw + 3) + 15) / 16 * 16 : Nat) : Int) := by
  decide

/-- The result's slot at `sw` words. -/
theorem setupMC_k : ∀ sw < 6, (setupMC sw).k.toInt = -((8 * (sw + 2) : Nat) : Int) := by
  decide

/-! ## `scc_rt_main` inside `RtM` -/

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {ar : Arena}
  {R : Region} {F : MachineData → Prop}

/-- **A covered block inside `RtM`** without `ret` (`hnr`) nor a branch to
the abort (`hna`): `blkW_rtMG` with its fall-through and its labels
positioned off the write abort (`hnext`, `hlabs`). -/
theorem blkW_rtM (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hl : l ∉ Spike.Lib.X64.AllocG.abLabs)
    (hnr : noRetBlk blk = true) (hna : "scc_rt_abort" ∉ blkLabs blk)
    (hnext : lastFalls blk = true → PosOff cells lab (lab l + Int64.ofNat (off + cellOff blk blk.length)))
    (hlabs : ∀ L ∈ blkLabs blk, PosOff cells lab (lab L)) :
    BlkW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n blk :=
  blkW_rtMG hI hpr hab hb he hok hR hlo hhi hph hl (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim)
    (fun h => by rw [hnr] at h; cases h) (fun h => Or.inl (hnext h)) (fun L hL _ => Or.inl (hlabs L hL))
    (fun _ _ _ k hk a ha hL => (noAbt hna k hk a ha hL).elim)

/-- A block without labels has no branch to the abort. -/
theorem noAb_nil {b : List (Directive × Nat)} (h : blkLabs b = []) : "scc_rt_abort" ∉ blkLabs b := by
  rw [h]; simp

/-- A closed side condition at `setupMC sw`: its labels and blocks unfolded. -/
local macro "sdec" : tactic =>
  `(tactic| (try simp only [setupMC]) <;> first | decide | rfl | simp [xLea, xCmp, xFr, xExit, Spike.Lib.X64.callB])

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states after a setup block are inside `RtM`**
(`MainSW` at `setupMC sw`, `sw < 6`), for any program with its code
(`hin`) and the runtime's (`hpr`, `hab`): its phase facts (`hph`), the
growth path, the setup block and the user function positioned off the
write abort (`hgrow`, `hset`, `hfn`), in any region holding its frame and
the return address its calls push (`hlo`, `hhi`). -/
theorem mainSW_rtM (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {sw : Nat} (hsw : sw < 6) (hin : mainSIn cells (setupMC sw) = true)
    (hph : MainPhS okPc ph lab (setupMC sw)) (hgrow : PosOff cells lab (lab (setupMC sw).grow))
    (hset : PosOff cells lab (lab (setupMC sw).setup)) (hfn : PosOff cells lab (lab (setupMC sw).fn))
    (hR : R.OK) (hlo : R.lo ≤ -8 - (setupMC sw).Z.toInt - 8) (hhi : 0 ≤ R.hi)
    {ms : MemSide isa} {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {g : Spike.Lib.X64.Flow.Ret0.MainG} {x0 : BitVec 64} :
    MainSW (RtM μ ar lab) (fun _ _ => False) exe endPc R F ms (setupMC sw) PostS Post g x0 := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hm8 : (-8 : Int64).toInt = -8 := by decide
  have hmf : noRetBlk (marshal (setupMC sw).sw (setupMC sw).fn) = true ∧
      blkLabs (marshal (setupMC sw).sw (setupMC sw).fn) = [(setupMC sw).fn] ∧
      lastFalls (marshal (setupMC sw).sw (setupMC sw).fn) = false := marshal_facts sw hsw
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, gE⟩, bCall⟩, -⟩, bMsh⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGapB hI.lays hgap
  have ee0 := label_labelGapB hI.lays gE
  rw [hI.labOk] at esc ee0
  have h4 : lab "scc_rt_main" + 1 + 3 = lab (setupMC sw).sc := by rw [esc, Int64.add_assoc]; rfl
  have hloZ : R.lo ≤ -8 - (setupMC sw).Z.toInt := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩ <;> rw [hI.labOk]
  · -- the head
    exact blkW_rtM hI hpr hab bHd (ofNat_zero' _) (xHead_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0)
      (by omega) (Int.le_refl _)) hR hloZ hhi (by have := hph.hd; rwa [ofNat_zero'] at this) (by sdec)
      xHead_noRet (by sdec)
      (fun _ => by
        have := posOff_of_blockAtB (lab := lab) bLea (by sdec) (by sdec)
        rw [ofNat_zero', esc] at this
        exact this)
      (labs_nil (by sdec))
  · -- the check's address
    exact blkW_rtM hI hpr hab bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _) hR hloZ hhi
      (by have := hph.lea; rwa [ofNat_zero', ← h4] at this) (by sdec) (xLea_noRet _ _) (noAb_nil (by sdec))
      (fun _ => posOff_of_blockAtB bLd (by sdec) (by sdec)) (labs_nil (by sdec))
  · -- the limit's load
    exact nodeW_rtM_fs (p := lab (setupMC sw).sc + Int64.ofNat 5) hI bLd rfl (by show _ + 1 + 3 + _ = _; rw [h4])
      hph.ld.1 (by rw [← ofNat_add']; exact notAb_of_blockAtB hI hpr hab bCmp (by sdec) (by sdec))
  · -- the check
    have e : lab (setupMC sw).sc + Int64.ofNat 14 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 := by rw [h4, ← ofNat_add']
    exact blkW_rtM hI hpr hab bCmp e (xCmp_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _) hR hloZ hhi
      (e ▸ hph.cmp) (by sdec) (xCmp_noRet _ _ _) (by sdec)
      (fun _ => posOff_of_blockAtB bFr (by sdec) (by sdec))
      (labs_one (L0 := (setupMC sw).grow) (by sdec) hgrow)
  · -- the frame
    have e : lab (setupMC sw).sc + Int64.ofNat 19 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 := by
      rw [h4, ← ofNat_add', ← ofNat_add', ← ofNat_add']
    exact blkW_rtM hI hpr hab bFr e (xFr_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _
        (fun p hp => by
          simp only [List.mem_singleton] at hp
          subst hp
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hm8]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi (e ▸ hph.fr) (by sdec) (xFr_noRet _ _ _) (noAb_nil (by sdec))
      (fun _ => by
        have := posOff_of_blockAtB (lab := lab) bCall (by sdec) (by sdec)
        rw [ofNat_zero', ee0] at this
        exact this)
      (labs_nil (by sdec))
  · -- the setup call
    exact blkW_rtM hI hpr hab bCall (ofNat_zero' _)
      (okBlk_callB (lo := -8 - (setupMC sw).Z.toInt - 8) (hi := 0) _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, Spike.Lib.X64.Rt.mainS1R, Spike.Lib.X64.Rt.oU, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi (by have := hph.call0; rwa [ofNat_zero'] at this) (by sdec) (callB_noRet _) (by sdec)
      (fun h => absurd h (by sdec)) (labs_one (L0 := (setupMC sw).setup) (by sdec) hset)
  · -- the marshalling block
    exact blkW_rtM hI hpr hab bMsh (ofNat_zero' _)
      (okBlk_marshal (lo := -8 - (setupMC sw).Z.toInt - 8) (hi := 0) (show sw ≤ 5 by omega) _
        (fun i hi => by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi (by have := hph.sp0; rwa [ofNat_zero'] at this) (by sdec) hmf.1
      (by rw [hmf.2.1]; sdec) (fun h => by rw [hmf.2.2] at h; cases h)
      (labs_one (L0 := (setupMC sw).fn) hmf.2.1 hfn)
  · -- the tail's block
    exact blkW_rtM hI hpr hab bEx (ofNat_zero' _)
      (xExit_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi (by have := hph.ex; rwa [ofNat_zero'] at this) (by sdec) (xExit_noRet _ _ _ _) (noAb_nil (by sdec))
      (fun _ => posOff_of_blockAtB bSvc (by sdec) (by sdec)) (labs_nil (by sdec))
  · -- the `exit_group`
    exact nodeW_rtM_exit (p := lab (setupMC sw).sp1 + Int64.ofNat 13) hI bSvc rfl
      (by
        show lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5 = _
        rw [← ofNat_add', ← ofNat_add'])
      hph.svc.1
      (fun σ _ hJ => by
        simp only [Reg64s.get64]
        apply BitVec.eq_of_toNat_eq
        rw [UInt64.toNat_toBitVec, hJ.1]; rfl)

end Main

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainPhS_of_tab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainPhS_of_tab

/-- info: 'Spike.Lib.LowerX64.mainPhS_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainPhS_of_placeOKAt

/-- info: 'Spike.Lib.LowerX64.blkW_rtM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_rtM

/-- info: 'Spike.Lib.LowerX64.mainSW_rtM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_rtM

end Spike.Lib.LowerX64
