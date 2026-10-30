/-
**wake.w's second `scc_rt_thread_init` call inside `W0`** (AArch64): every
node of the call from `wc_main` (returning to `.sp6`) on the second TCB inside
the start's level `StartWf.WS`, towards `wake_wc_mid_hatW`'s `hti`. Each node's
`SFactsSt` at the second instance are `Rt.tiW_gen`'s at `ph2b` (`instOk2bP`,
`tiPh2b`) at the dummy control `A64Consumer.c0` (`Ti2C0.tiW_c0`), moved inside `WS` by `StartTi.blk2_WS` / `node2_WSst` (the TCB
fields' stores), the nested `scc_rt_stack_take` call by `take2W_WS`. The
second TCB's words are outside `rtWords`: their mapping, absence under `F`
and being off `own2b` are premises (`hmF`, `hunF`, `hnoF`).

- `ti2_WS`: the call's node obligations inside `WS`.
-/
import Spike.Lib.A64WakeStartTiT3
import Spike.Lib.A64WakeTi2T3

namespace Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.Tcb2W (soRun)
open Spike.Lib.A64.Flow.Ret0 (TI TiG TiW tiN tiTake StackM stacksA pinA rAddr_x10)
open Spike.Lib.A64.Flow.Ret0.ThreadInit
open Spike.Lib (Arena FragS)
open Spike.Lib.A64.WakePh.Ti2 (BandP bandP_callee bandP_mono fin2)

/-- `hso` of a block of `scc_rt_thread_init` at offsets `o`, decided. -/
local macro "soI " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 0
    by decide) k hk)

set_option hygiene false in
/-- A store of TCB field `j` (`str x9, [x10, #8·j]`, block `b`) inside `WS`. -/
local macro "tstW " b:term:max j:term:max : tactic =>
  `(tactic| focus
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb := by
      simp [Spike.Lib.A64.Rt.Ti.tiAddrs]
    have hra' : ∀ (r : Reg64s), r.X10.toBitVec = q.tcb →
        Spike.Lib.A64.Flow.rAddr r .X10 (Int64.ofNat (8 * $j)) = q.tcb + BitVec.ofNat 64 (8 * $j) :=
      fun r h => by rw [rAddr_x10 h]; rfl
    refine node2_WSst hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 $b rfl h
      (hP.st (storePc L.lab $j) (by simp [Spike.Lib.A64.Rt.Ti.stPcs])).1
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [tiN]; decide) (by decide +kernel) (fun σ c h => h.1.trans hq)
      (fun σ c m hJ hF => ?_) (fun σ c m hJ hF => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ $b) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; simp [tiN])
      have hdm : Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 (Int64.ofNat (8 * $j))) 8
          = none := by
        dsimp only [tiN] at hJ
        rw [hA.regs, hra' _ hJ.2.2.2]
        exact hunF _ ha _ hF.1
      exact ⟨keep_str hc hd hdm hs, by rw [keep_pc hc (keep_str hc hd hdm hs), hp']; rfl⟩
    · dsimp only [tiN, storePc]; rw [eSp]; decide
    · dsimp only [tiN] at hJ
      rw [hra' _ hJ.2.2.2]; exact hunF _ ha _ hF.1
    · dsimp only [tiN] at hJ
      rw [hra' _ hJ.2.2.2]; exact hoffT _ ha)

section Gen

variable {P : MachineData → Prop}
variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.A64.Flow.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbdI : BandP L R (-256))

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbdI

set_option maxHeartbeats 3200000 in
/-- **The second `scc_rt_thread_init`'s node obligations inside `WS`**,
called from `wc_main` returning to `.sp6` (`hra`), on the second TCB: the
frames `[-256, 0]` of the callee's region on the pool (`hbdI`), the TCB's
fields mapped, unset under `F` and off `own2b` (`hmF`, `hunF`, `hnoF`); the
TCB's fields, the lock's and the next offset's words off the arena and not its
counter word (`hoffT`, `hoffL`, `hoffX`); `X0` off the take site by `hX0`,
at it from the site's range, frame, the site frame `P`, the caller's cells outside the take's
region (`CallerCells`, carried by `TiW`'s `.call`) and the take's cells
(`hXs`). -/
theorem ti2_WS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TiG) (hq : q.c0 = c0)
    (hmF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨b, 8⟩ = true)
    (hunF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, ∀ j w, (⟨b, 8⟩, w) ∉ own2b L a j)
    (hra : q.g.ra = (L.lab ".L21_wc_main.sp6").toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hSMt : Spike.Lib.A64.Flow.FStable (R.callee oI.sp (-208) 0) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      Spike.Lib.A64.Flow.Ret0.CallerCells R oI.sp (-208) 0 s.st.1 →
      (∀ k, (R.callee oI.sp (-208) 0).Off k →
        (Mem.loadInt s.st.1.dmem ((R.callee oI.sp (-208) 0).addr k) 8).isSome) → X0 s) :
    ∀ i, TiW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      (StackM rS) q i P := by
  have hrc : Spike.Lib.A64.Rt.RtCodeIn0 L.prog := hp ▸ wake_rtCodeIn0
  have hPl2 : ∀ m m', (F m ∧ StackM rS m) → Spike.Lib.A64.Flow.DFrame R m m' → Pl m' :=
    fun m m' h hd => hPl m m' h.1 hd
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.A64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  -- the nodes' state facts at any control: `tiW_gen` at the dummy control `c0` (`cfacts_c0`), moved by
  -- `Ti2C0.tiW_c0`; the real control's facts (its placement) enter at `blk2_WS` / `node2_WSst` (`hc0`, `hpl0`)
  have hT := Spike.Lib.A64.WakePh.Ti2C0.tiW_c0 (P := P) (c0' := Spike.Lib.A64Consumer.c0)
    (fun s _ c' (h : Spike.Lib.A64Consumer.SFacts L.Λ _ _ rS _ (fun _ => none) s c') => h.toSt) <|
    Spike.Lib.A64.Rt.tiW_gen (rS := rS) (lbl := fun _ => none) (instOk2bP (rS := rS) hp hlo a hsite)
    (fun _ => rfl) hrc.ti Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hR hal hRlo hhi _ rfl hra (tiPh2b hΛ hlab)
    hmF hunF hnoF hsub hSM hSMt hrc.take
    (takePh2b hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
      hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.A64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.A64.PhRec.rtF_next (hFr m hm)) hrS hro
  have hP := tiPh2b (L := L) hΛ hlab
  have hbd48 : BandP L R (-48) := bandP_mono hbdI (by decide)
  obtain ⟨eFn, eEn⟩ := ti_labs hlab (L := L)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, eSp⟩ := take_labs hlab (L := L)
  have hin := wake_rtCodeIn0.ti
  simp only [threadInitIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bSp⟩, bS0⟩, bF1⟩, bS1⟩, bF2⟩, bS2⟩, bF3⟩, bS3⟩, bF4⟩, bS4⟩, bF5⟩, bS5⟩,
    bRet⟩ := hin
  rw [Spike.Lib.A64.Rt.Ti.st0_eq] at bS0; rw [Spike.Lib.A64.Rt.Ti.st1_eq] at bS1
  rw [Spike.Lib.A64.Rt.Ti.st2_eq] at bS2; rw [Spike.Lib.A64.Rt.Ti.st3_eq] at bS3
  rw [Spike.Lib.A64.Rt.Ti.st4_eq] at bS4; rw [Spike.Lib.A64.Rt.Ti.st5_eq] at bS5
  intro i
  have h := hT i
  cases i <;> dsimp only [TiW] at h ⊢
  case e =>
    refine blk2_WS (rl := fnL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd48 bE (Spike.Lib.A64.Flow.ofNat4_zero _)
      tiPro_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.e) ?_ (soI tiPro oE)
      (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiPro oE)) (by decide +kernel)
      (nrB Spike.Lib.A64.Rt.Ti.tiPro_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eFn]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiPro_walk _ _ hJ.2).1, eFn]; decide
  case entry =>
    refine blk2_WS (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd48 bEn (Spike.Lib.A64.Flow.ofNat4_zero _)
      tiCall_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.entry) ?_ (soI tiCall oI)
      (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiCall oI)) (by decide +kernel)
      (nrB Spike.Lib.A64.Rt.Ti.tiCall_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eEn]; revert k; decide
    · obtain ⟨eT, -⟩ := take_labs hlab (L := L)
      dsimp only [tiN] at hJ ⊢; rw [(tiCall_walk _ _ hJ.2).1, eT]; decide
  case call =>
    intro g hg j
    obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := oI.sp) (lo' := -208) hR hal
      (by show R.lo ≤ -48 + -208; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    exact take2W_WS hp hlo hlab hsite hcl hc0 hpl0 (fun m m' h hd => hPl m m' h.1 (dframe_of_callee hR
        (show R.lo ≤ -48 + -208 by omega) (by decide) (show (-48 : Int) < R.hi by omega) hd)) hX0
      (bandP_callee hbdI (by show (-256 : Int) ≤ -48 + -208; omega) (by decide)) hΛ hs hro hR' hal'
      (by show (-208 : Int) ≤ -208; omega) (by show (0 : Int) ≤ 0; omega) (fun m h => hFr m h.1) (tiTake q g)
      hq hg hrS hsub hSMt hoffL hoffX (fun s hpc hr h hz hk => hXs s hpc hr h.1 hz h.2 hk) j
  case sp =>
    refine blk2_WS (rl := spL) hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bSp (Spike.Lib.A64.Flow.ofNat4_zero _)
      tiSp_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.sp) ?_ (soI tiSp oI)
      (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiSp oI)) (by decide +kernel)
      (nrB Spike.Lib.A64.Rt.Ti.tiSp_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiSp_walk _ _ hJ.2.1 hJ.2.2).1, eSp]; decide
  case st0 => tstW bS0 0
  case f1 =>
    refine blk2_WS (rl := spL) hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bF1 rfl tiF1_ok hR hal (by omega) (by omega)
      h (okPc_of_blkPh hP.f1) ?_ (soI tiF1 oI) (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiF1 oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Ti.tiF1_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiF1_walk _ _ hJ.2).1, eSp]; decide
  case st1 => tstW bS1 1
  case f2 =>
    refine blk2_WS (rl := spL) hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bF2 rfl tiF2_ok hR hal (by omega) (by omega)
      h (okPc_of_blkPh hP.f2) ?_ (soI tiF2 oI) (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiF2 oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Ti.tiF2_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiF2_walk _ _ hJ.2).1, eSp]; decide
  case st2 => tstW bS2 2
  case f3 =>
    refine blk2_WS (rl := spL) hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bF3 rfl tiF3_ok hR hal (by omega) (by omega)
      h (okPc_of_blkPh hP.f3) ?_ (soI tiF3 oI) (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiF3 oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Ti.tiF3_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiF3_walk _ _ hJ.2).1, eSp]; decide
  case st3 => tstW bS3 3
  case f4 =>
    refine blk2_WS (rl := spL) hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bF4 rfl tiF4_ok hR hal (by omega) (by omega)
      h (okPc_of_blkPh hP.f4) ?_ (soI tiF4 oI) (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiF4 oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Ti.tiF4_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiF4_walk _ _ hJ.2).1, eSp]; decide
  case st4 => tstW bS4 4
  case f5 =>
    refine blk2_WS (rl := spL) hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bF5 rfl tiF5_ok hR hal (by omega) (by omega)
      h (okPc_of_blkPh hP.f5) ?_ (soI tiF5 oI) (fin2 hlab hbd48 (fun σ c hJ => ?_) (soI tiF5 oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Ti.tiF5_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ ⊢; rw [(tiF5_walk _ _ hJ.2).1, eSp]; decide
  case st5 => tstW bS5 5
  case ret =>
    refine blk2_WS (rl := ".L21_wc_main.sp6") hp hlo hlab hsite hcl hc0 hpl0 hPl2 hX0 hbd48 bRet rfl tiRet_ok
      hR hal (by omega) (by omega) h (okPc_of_blkPh hP.ret) ?_ (soI tiRet oI) (fun σ c hJ s m _ _ _ hs' => ?_)
      (by decide +kernel) (Spike.Lib.A64Consumer.hret_of_run tiRet_ok fun σ c hJ => ?_) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eSp]; revert k; decide
    · dsimp only [tiN] at hJ hs'
      rw [(tiRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec] at hs'
      obtain ⟨-, -, -, -, -, h6, hg, -, -⟩ := Spike.Lib.A64.WakePh.labs_eq hlab (L := L)
      exact .inr (.inl ⟨by unfold pcOf; rw [hs']; exact Nat.le_refl _, by unfold pcOf; rw [hs']; dsimp only; omega⟩)
    · dsimp only [tiN] at hJ ⊢
      rw [(tiRet_walk _ _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTi.ti2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ti2_WS

end Spike.Lib.A64.WakePh.StartTi
