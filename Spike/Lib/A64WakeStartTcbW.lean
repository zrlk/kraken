/-
**wake.w's first `scc_rt_alloc_tcb` call inside `W0`** (AArch64): every
node of the call from `scc_rt_start` (returning to `.sp2`) inside the
start's level `StartWf.WS`, the shape of `StartWf.startEW_W0S`'s `htcb`.
Each node's `SFacts` at the first instance are `Rt.tcbW_gen`'s at `phW`
(`instOkWS`, `tcbPhW`), moved inside `WS` by `StartTcb.blkT_WS` /
`nodeT_WS` / `nodeT_WSldop` (the counter's add) / `nodeT_WSst` (the
header's store).

- `startTcb_WS`: the call's node obligations inside `WS`.
-/
import Spike.Lib.A64WakeStartTcbL

namespace Spike.Lib.A64.WakePh.StartTcb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.Tcb2W (soRun tcb_labs wake_allocTcbIn keep_rmw keep_hdr)
open Spike.Lib.A64.WakePh.WcW (freeN freeAt freeAt_lab goodW_of_freeN cv inCv)
open Spike.Lib.A64.Flow.Ret0 (TN)
open Spike.Lib.A64.Flow.Ret0.AllocTcb
open Spike.Lib (Arena FragS)

/-- A covered block's pcs are off the sites (`blkPh`'s first conjunct). -/
private theorem okB {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List Directive} (h : Spike.Lib.A64Consumer.blkPh okP phf d lab pc ra blk = true) :
    ∀ j < blk.length, okP (pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -192 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 0
    by decide) k hk)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl' : Lbl}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s → X0 s)
  (hbd : BandT L (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0))

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd


set_option maxHeartbeats 3200000 in
/-- **`scc_rt_alloc_tcb`'s node obligations inside `WS`**, called from
`scc_rt_start` returning to `.sp2` (`htcb` of `startEW_W0S`): the frame
`[-192, 0]` of the callee's region off the pool (`hbd`), the counter's and
the first header's words off the arena and not its counter word (`hoffP`,
`hoffH`). -/
theorem startTcb_WS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a) {n0 : BitVec 64}
    (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (hn0 : n0 = 0#64)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffH : ¬ (ar.heap ≤ L.pinA.toNat ∧ L.pinA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ g, g.ra = (L.lab ".L0_scc_rt_start.sp2").toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TcbW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F ⟨g, n0, c0⟩ i := by
  subst hn0
  intro g hg
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -192)
    hR hal (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
  have hlo2 : (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0).lo ≤ -192 := by show (-192 : Int) ≤ -192; omega
  have hhi2 : 0 ≤ (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0).hi := by show (0 : Int) ≤ 0; omega
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h0 : ∃ j < 7, L.pinA + 0#64 = L.pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hP := tcbPhW (Λ := L.Λ) (a := a) hΛ hlab hs
  have hT := Spike.Lib.A64.Rt.tcbW_gen (rS := rS) (lbl := lbl') (instOkWS (a := a) (rS := rS) hp hlo hlab) (fun _ => rfl)
    (hp ▸ wake_allocTcbIn) hC0 hR' hal' hlo2 hhi2 ⟨g, 0#64, c0⟩ rfl hg hP
    (by rw [hpn]; exact (L.words_mapped _ L.pn_mem).1)
    (by rw [hpin]; exact Spike.Lib.A64.PhRec.mapped_tcb h0)
    (fun m hm => by rw [hpn]; exact Spike.Lib.A64.PhRec.rtF_pn (hFr m hm))
    (fun m hm => by rw [hpin]; exact Spike.Lib.A64.PhRec.rtF_tcb (hFr m hm) h0)
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := tcb_labs hlab (L := L)
  have hin := wake_allocTcbIn
  simp only [allocTcbIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := hin
  have nr : ∀ {blk : List Directive}, Spike.Lib.A64Consumer.noRetBlk blk = true → ∀ {n : ND} {lb : Label → Int64}
      {ra' : Int64}, ∀ σ (c : Ctl), n.J σ c → ∀ j (hj : j < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lb (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hb j hj r hr).elim
  intro i
  have h := hT i
  cases i <;> dsimp only [Spike.Lib.A64.Flow.Ret0.TcbW] at h ⊢
  case e =>
    refine blkT_WS (rl := fnL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bE (Spike.Lib.A64.Flow.ofNat4_zero _) atPro_ok hR' hal' (by omega)
      (by omega) h (okB hP.e) ?_ (soT atPro oE) (finT hlab hbd (fun σ c hJ => ?_) (soT atPro oE))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atPro_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eFn]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [(atPro_walk _ _ hJ.2).1, eFn]; decide
  case entry =>
    refine blkT_WS (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bEn (Spike.Lib.A64.Flow.ofNat4_zero _) atChk_ok hR' hal'
      (by omega) (by omega) h (okB hP.entry) ?_ (soT atChk oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atChk oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atChk_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eEn]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [(atChk_walk _ _ hJ.2).1, eEn]; decide
  case j1 =>
    refine blkT_WS (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bJ1 rfl atJ1_ok hR' hal' (by omega) (by omega) h
      (okB hP.j1) ?_ (soT atJ1 oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atJ1 oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atJ1_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eEn]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [atJ1_run]; dsimp only; rw [eLen]; decide
  case len =>
    refine blkT_WS (rl := lenL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bLen (Spike.Lib.A64.Flow.ofNat4_zero _) atLen_ok hR' hal'
      (by omega) (by omega) h (okB hP.len) ?_ (soT atLen oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atLen oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atLen_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [(atLen_walk _ _ hJ.2).1, eLen]; decide
  case arg =>
    refine blkT_WS (rl := lenL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bArg rfl atArg_ok hR' hal' (by omega) (by omega) h
      (okB hP.arg) ?_ (soT atArg oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atArg oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atArg_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [(atArg_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide
  case bnd =>
    refine blkT_WS (rl := lenL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bBnd rfl atBnd_ok hR' hal' (by omega) (by omega) h
      (okB hP.bnd) ?_ (soT atBnd oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atBnd oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atBnd_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢
      rw [(atBnd_walk _ _ hJ.2.1 hJ.2.2 (by decide)).1, eLen]; decide
  case j2 =>
    refine blkT_WS (rl := lenL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bJ2 rfl atJ2_ok hR' hal' (by omega) (by omega) h
      (okB hP.j2) ?_ (soT atJ2 oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atJ2 oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atJ2_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [atJ2_run]; dsimp only; rw [eOk]; decide
  case ok2 =>
    refine blkT_WS (rl := okL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bO2 rfl atOk_ok hR' hal' (by omega) (by omega) h
      (okB hP.ok2) ?_ (soT atOk oI) (finT hlab hbd (fun σ c hJ => ?_) (soT atOk oI))
      (by decide +kernel) (nr Spike.Lib.A64.Rt.Tcb.atOk_noRet) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eOk]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢; rw [(atOk_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide
  case ret =>
    refine blkT_WS (rl := Spike.Lib.A64.Flow.Ret0.sp2L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bRet rfl atRet_ok hR' hal' (by omega)
      (by omega) h (okB hP.ret) ?_ (soT atRet oI) (fun σ c hJ s m _ _ _ hs' => ?_) (by decide +kernel)
      (Spike.Lib.A64Consumer.hret_of_run atRet_ok fun σ c hJ => ?_) (fun _ _ h => h.1)
    · intro k hk; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eOk]; revert k; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ hs'
      rw [(atRet_walk _ _ hJ.2).1, hg, Int64.ofBitVec_toBitVec] at hs'
      exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_lab hlab (by wsfree_dec))
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ ⊢
      rw [(atRet_walk _ _ hJ.2).1, hg]; exact Int64.ofBitVec_toBitVec _
  case adrp =>
    refine nodeT_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bA rfl h (hP.si _ (by simp [Spike.Lib.A64.Rt.Tcb.siPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; decide)
      (by decide +kernel) (fun _ _ h => h.1)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bA) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; simp)
      exact ⟨keep_adrp hc hs, by rw [keep_pc hc (keep_adrp hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; decide
  case add =>
    refine nodeT_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bA1 rfl h (hP.si _ (by simp [Spike.Lib.A64.Rt.Tcb.siPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; decide)
      (by decide +kernel) (fun _ _ h => h.1)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bA1) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; simp)
      exact ⟨keep_add hc hs, by rw [keep_pc hc (keep_add hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eLen]; decide
  case ok =>
    refine nodeT_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bO (Spike.Lib.A64.Flow.ofNat4_zero _) h
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Tcb.siPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; decide)
      (by decide +kernel) (fun _ _ h => h.1)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bO) (Spike.Lib.A64.Flow.ofNat4_zero _) s he
        hn).cell (j := 0) rfl rfl rfl (by rw [hp']; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; simp)
      exact ⟨keep_adrp hc hs, by rw [keep_pc hc (keep_adrp hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eOk]; decide
  case ok1 =>
    refine nodeT_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bO1 rfl h (hP.si _ (by simp [Spike.Lib.A64.Rt.Tcb.siPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; decide)
      (by decide +kernel) (fun _ _ h => h.1)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bO1) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; simp)
      exact ⟨keep_add hc hs, by rw [keep_pc hc (keep_add hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; rw [eOk]; decide
  case rmw =>
    refine nodeT_WSldop hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bRmw rfl h hP.rmwOk
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; decide)
      (by decide +kernel) (fun _ _ h => h.1) (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bRmw) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; simp)
      have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
        dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ
        rw [hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hpn]
        exact Spike.Lib.A64.PhRec.rtF_pn (hFr _ hF)
      exact ⟨keep_rmw hc hd hdm hs, by rw [keep_pc hc (keep_rmw hc hd hdm hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN, rmwPc]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN, rmwPc]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hpn]; exact Spike.Lib.A64.PhRec.rtF_pn (hFr _ hF)
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hpn]; exact hoffP
  case hdr =>
    refine nodeT_WSst hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bH rfl h
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Tcb.siPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; decide)
      (by decide +kernel) (fun _ _ h => h.1) (fun σ c m hJ hF => ?_) (fun σ c m hJ hF => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bH) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN]; simp)
      dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ
      have ha : BitVec.ofInt 64 ((s.st.1.regs.getXReg .X10).toBitVec.toInt + (0 : Int64).toInt) =
          Spike.Lib.A64.Flow.Ret0.pinA L.lab + 0#64 := by
        rw [hA.regs, ← hJ.2.2.2]; simp [Reg64s.getXReg]
      have hdm : Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.Ret0.pinA L.lab + 0#64) 8 = none := by
        rw [hpin]; exact Spike.Lib.A64.PhRec.rtF_tcb (hFr _ hF) h0
      exact ⟨keep_hdr hc hd ha hdm hs, by rw [keep_pc hc (keep_hdr hc hd ha hdm hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN, hdrPc]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN, hdrPc]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hpin]
      exact Spike.Lib.A64.PhRec.rtF_tcb (hFr _ hF) h0
    · dsimp only [Spike.Lib.A64.Flow.Ret0.tcbN] at hJ
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hpin, BitVec.add_zero]
      exact hoffH

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.startTcb_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startTcb_WS

end Spike.Lib.A64.WakePh.StartTcb
