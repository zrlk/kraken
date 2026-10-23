/-
**`scc_rt_stack_take`'s states inside `W`, for any program** (`takeW_gen`):
the obligations `TakeW` (`Spike/Lib/A64Ret0.lean`) of every node of
`scc_rt_stack_take`'s feasible path, from an instance's facts (`InstOk`),
the function's code (`stackTakeIn`, a field of `RtCodeIn`), its phase facts
(`TakePh`), the three words it accesses and the range it takes.

- **The phase facts** (`TakePh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), no dead target; each label pair's
  instructions off the sites in their next pc's phase; no node before the
  site in the take's phase; the lock `scc_rt_stack_lock` owned at its swap
  and its release and set by them, `scc_rt_stack_next` owned at its add and
  updated by it, the free count's load in its next pc's phase.
- **The take site**: off the release and abort sites, the marks' take site,
  its next pc in the take's phase with the same owned words; the range named
  by `x0`/`x1` in the pool (`hrS`, `hsub`), the read-only data off the pool
  (`hdisj`).
- **The words**: `scc_rt_stack_lock`, `scc_rt_stack_next` (written) and
  `scc_rt_stack_free_n` (read) mapped in the loaded kernel state and
  unmapped in private memory under the frame condition.
- **Oracle**: `ret0.w`'s `takeSiteW` and `takeW` (`Spike/Lib/A64Ret0I.lean`)
  are this at its instance (`Spike/Test/A64RtTake.lean`).
-/
import Spike.Lib.Rt.A64RtTcb

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW takeNG labMid lockA freeNA nextA stacksA StackM ofNat4_succ')
open Scc.Cert.Rt.A64 (blockAt)

namespace Take

open Spike.Lib.A64.Flow.Ret0.StackTake

/-- The pcs of the label pairs' instructions: `scc_rt_stack_free_n`,
`scc_rt_stack_free`, `scc_rt_stack_lock` (twice), `scc_rt_stack_next` and
`scc_rt_stacks`. -/
def siPcs (lab : Label → Int64) : List Int64 :=
  [lab doneL + Int64.ofNat (4 * 0), lab doneL + Int64.ofNat (4 * 1), lab doneL + Int64.ofNat (4 * 7),
    lab doneL + Int64.ofNat (4 * 8), lab doneL + Int64.ofNat (4 * 14), lab doneL + Int64.ofNat (4 * 15),
    lab bumpL + Int64.ofNat (4 * 0), lab bumpL + Int64.ofNat (4 * 1), lab bumpL + Int64.ofNat (4 * 6),
    lab bumpL + Int64.ofNat (4 * 7), lab okL + Int64.ofNat (4 * 0), lab okL + Int64.ofNat (4 * 1)]

/-- The pcs before the take: the nodes' up to the site, and the pcs after
the swap, the release and the add. -/
def takePcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat (4 * 0), lab entryL + Int64.ofNat (4 * 0), lab clsL + Int64.ofNat (4 * 0),
    lab clsL + Int64.ofNat (4 * 4), lab doneL + Int64.ofNat (4 * 2), lab doneL + Int64.ofNat (4 * 9),
    lab doneL + Int64.ofNat (4 * 16), lab spinL + Int64.ofNat (4 * 0), lab spinL + Int64.ofNat (4 * 2),
    lab spinL + Int64.ofNat (4 * 2) + Int64.ofNat 4, lab spinL + Int64.ofNat (4 * 3),
    lab lockedL + Int64.ofNat (4 * 0), lab lockedL + Int64.ofNat (4 * 1), lab lockedL + Int64.ofNat (4 * 2),
    lab bumpL + Int64.ofNat (4 * 2), lab bumpL + Int64.ofNat (4 * 5), lab bumpL + Int64.ofNat (4 * 5) + Int64.ofNat 4,
    lab bumpL + Int64.ofNat (4 * 8), lab bumpL + Int64.ofNat (4 * 11),
    lab bumpL + Int64.ofNat (4 * 11) + Int64.ofNat 4, lab bumpL + Int64.ofNat (4 * 12),
    lab bumpL + Int64.ofNat (4 * 21), lab okL + Int64.ofNat (4 * 2), lab takenL + Int64.ofNat (4 * 0),
    lab siteL + Int64.ofNat (4 * 0)] ++ siPcs lab

/-- **`scc_rt_stack_take`'s phase facts** at labels `lab`, phase index `ph`,
off-site pcs `okPc`, owned words by phase `ownOf`, marks `μ`, returning to
`ra siteL`. -/
structure TakePh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (μ : Marks) (lab ra : Label → Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat (4 * 0)) (ra fnL) stPro = true
  entry : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 0)) (ra entryL) stInit = true
  cls : blkPh okPc ph (fun _ => false) lab (lab clsL + Int64.ofNat (4 * 0)) (ra clsL) stCls = true
  j1 : blkPh okPc ph (fun _ => false) lab (lab clsL + Int64.ofNat (4 * 4)) (ra clsL) stJ1 = true
  d2 : blkPh okPc ph (fun _ => false) lab (lab doneL + Int64.ofNat (4 * 2)) (ra doneL) stFreeN = true
  d9 : blkPh okPc ph (fun _ => false) lab (lab doneL + Int64.ofNat (4 * 9)) (ra doneL) stFree = true
  d16 : blkPh okPc ph (fun _ => false) lab (lab doneL + Int64.ofNat (4 * 16)) (ra doneL) stLock = true
  sp0 : blkPh okPc ph (fun _ => false) lab (lab spinL + Int64.ofNat (4 * 0)) (ra spinL) stSwp = true
  sp3 : blkPh okPc ph (fun _ => false) lab (lab spinL + Int64.ofNat (4 * 3)) (ra spinL) stSpin = true
  lk0 : blkPh okPc ph (fun _ => false) lab (lab lockedL + Int64.ofNat (4 * 0)) (ra lockedL) stLdN = true
  lk2 : blkPh okPc ph (fun _ => false) lab (lab lockedL + Int64.ofNat (4 * 2)) (ra lockedL) stEmpty = true
  b2 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat (4 * 2)) (ra bumpL) stUnl = true
  b8 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat (4 * 8)) (ra bumpL) stAdd = true
  b12 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat (4 * 12)) (ra bumpL) stBnd = true
  b21 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat (4 * 21)) (ra bumpL) stJ2 = true
  ok2 : blkPh okPc ph (fun _ => false) lab (lab okL + Int64.ofNat (4 * 2)) (ra okL) stOk = true
  tk : blkPh okPc ph (fun _ => false) lab (lab takenL + Int64.ofNat (4 * 0)) (ra takenL) stSite = true
  ret : blkPh okPc ph (fun _ => false) lab (lab siteL + Int64.ofNat (4 * 1)) (ra siteL) stRet = true
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat
  swpOk : okPc (swpPc lab).toBitVec.toNat = true
  ldnOk : okPc (freeNPc lab).toBitVec.toNat = true
  unlOk : okPc (unlPc lab).toBitVec.toNat = true
  nxtOk : okPc (nextPc lab).toBitVec.toNat = true
  ldnPh : ph (freeNPc lab + Int64.ofNat 4).toBitVec.toNat = ph (freeNPc lab).toBitVec.toNat
  noTk : ∀ p ∈ takePcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  swpIn : ∃ v, (⟨lockA lab, 8⟩, v) ∈ ownOf (ph (swpPc lab).toBitVec.toNat)
  swpUpd : ownUpdB (ownOf (ph (swpPc lab).toBitVec.toNat)) (ownOf (ph (swpPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨lockA lab, 8⟩ (fun _ => (1#64 : BitVec 64).setWidth 128) = true
  unlIn : ∃ v, (⟨lockA lab, 8⟩, v) ∈ ownOf (ph (unlPc lab).toBitVec.toNat)
  unlUpd : ownUpdB (ownOf (ph (unlPc lab).toBitVec.toNat)) (ownOf (ph (unlPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨lockA lab, 8⟩ (fun _ => (0#64 : BitVec 64).setWidth 128) = true
  nxtIn : ∃ v, (⟨nextA lab, 8⟩, v) ∈ ownOf (ph (nextPc lab).toBitVec.toNat)
  nxtUpd : ownUpdB (ownOf (ph (nextPc lab).toBitVec.toNat)) (ownOf (ph (nextPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨nextA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) size0).setWidth 128) = true
  siteRel : ∀ a, μ.site .release = some a → (lab siteL).toBitVec.toNat ≠ a
  siteAb : ∀ k a, μ.abortAt k = some a → (lab siteL).toBitVec.toNat ≠ a
  siteAt : μ.site .take = some (lab siteL).toBitVec.toNat
  siteOwn : ownOf (ph (lab siteL + Int64.ofNat 4).toBitVec.toNat) = ownOf (ph (lab siteL).toBitVec.toNat)
  tk4 : ∀ s : State, pcOf s = (lab siteL + Int64.ofNat 4).toBitVec.toNat → Tk s

theorem stPro_noRet : noRetBlk stPro = true := by rfl
theorem stInit_noRet : noRetBlk stInit = true := by rfl
theorem stCls_noRet : noRetBlk stCls = true := by rfl
theorem stJ1_noRet : noRetBlk stJ1 = true := by rfl
theorem stFreeN_noRet : noRetBlk stFreeN = true := by rfl
theorem stFree_noRet : noRetBlk stFree = true := by rfl
theorem stLock_noRet : noRetBlk stLock = true := by rfl
theorem stSwp_noRet : noRetBlk stSwp = true := by rfl
theorem stSpin_noRet : noRetBlk stSpin = true := by rfl
theorem stLdN_noRet : noRetBlk stLdN = true := by rfl
theorem stEmpty_noRet : noRetBlk stEmpty = true := by rfl
theorem stUnl_noRet : noRetBlk stUnl = true := by rfl
theorem stAdd_noRet : noRetBlk stAdd = true := by rfl
theorem stBnd_noRet : noRetBlk stBnd = true := by rfl
theorem stJ2_noRet : noRetBlk stJ2 = true := by rfl
theorem stOk_noRet : noRetBlk stOk = true := by rfl
theorem stSite_noRet : noRetBlk stSite = true := by rfl

end Take

section Pair

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A label address pair** `adrp x9, L; add x9, x9, :lo12:L` at `l`, `k`
before the take: both nodes inside `SFacts`, each off the sites, in its next
pc's phase and not in the take's phase. -/
theorem pairW_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {L l : Label} {k : Nat} {sp : Int} {n : ND}
    (hb1 : blockAt prog l k [(SI.adrp .X9 L).toDir] = true)
    (hb2 : blockAt prog l (k + 1) [(SI.addLo12 .X9 .X9 L).toDir] = true)
    (hp : n.pc = lab l + Int64.ofNat (4 * k)) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hs1 : okPc (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true ∧
      ph (lab l + Int64.ofNat (4 * k) + Int64.ofNat 4).toBitVec.toNat = ph (lab l + Int64.ofNat (4 * k)).toBitVec.toNat)
    (hs2 : okPc (lab l + Int64.ofNat (4 * (k + 1))).toBitVec.toNat = true ∧
      ph (lab l + Int64.ofNat (4 * (k + 1)) + Int64.ofNat 4).toBitVec.toNat =
        ph (lab l + Int64.ofNat (4 * (k + 1))).toBitVec.toNat)
    (hT1 : ∀ s : State, pcOf s = (lab l + Int64.ofNat (4 * k)).toBitVec.toNat → ¬ Tk s)
    (hT2 : ∀ s : State, pcOf s = (lab l + Int64.ofNat (4 * (k + 1))).toBitVec.toNat → ¬ Tk s) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n ∧
      NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (labMid lab l L k sp n.J) :=
  ⟨nodeW_si_pre hI hb1 rfl hp hC hs1.1 hT1 hs1.2,
    nodeW_si_pre hI hb2 rfl (ofNat4_succ' _ _) (fun _ c ⟨_, hJ, _⟩ => hC _ c hJ) hs2.1 hT2 hs2.2⟩

end Pair

set_option maxHeartbeats 800000 in
open Take Spike.Lib.A64.Flow.Ret0.StackTake in
/-- **`scc_rt_stack_take`'s states are inside `SFacts`**, for any program
with the function's code (`hin`), in any region holding its frame, with the
source control `c0` (`hC0`, its facts), returning to `ra siteL` (`hra`), its
phase facts (`hph`), its three words mapped (`hmL`, `hmN`, `hmX`) and
unmapped in private memory under the frame condition (`hunL`, `hunN`,
`hunX`), the range taken named by the site's registers (`hrS`) in the pool
(`hsub`), off the read-only data (`hdisj`) and kept by the region's writes
(`hSM`). -/
theorem takeW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : stackTakeIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi) (q : TakeG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra siteL).toBitVec) (hph : TakePh okPc ph Tk ownOf μ lab ra)
    (hmL : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨lockA lab, 8⟩ = true)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨freeNA lab, 8⟩ = true)
    (hmX : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨nextA lab, 8⟩ = true)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hrS : rS = ⟨(stacksA lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub Λ.stackPool)
    (hdisj : Λ.rodata.Disjoint Λ.stackPool) (hSM : FStable R (StackM rS)) :
    ∀ i, TakeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (StackM rS) q i := by
  have h := hin
  simp only [stackTakeIn, labIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bCls⟩, bJ1⟩, ⟨bD0, bD1⟩⟩, bD2⟩, ⟨bD7, bD8⟩⟩, bD9⟩,
    ⟨bD14, bD15⟩⟩, bD16⟩, bSp0⟩, bSwp⟩, bSp3⟩, bLk0⟩, bLdn⟩, bLk2⟩, ⟨bB0, bB1⟩⟩, bB2⟩, bUnl⟩, ⟨bB6, bB7⟩⟩,
    bB8⟩, bNxt⟩, bB12⟩, bB21⟩, ⟨bOk0, bOk1⟩⟩, bOk2⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ takePcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnr : ∀ {blk : List Directive}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim
  intro i
  cases i
  case e =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bE (ofNat4_zero _) stPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr stPro_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case entry =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bEn (ofNat4_zero _) stInit_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1)
      hph.entry (hnr stInit_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case cls =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bCls (ofNat4_zero _) stCls_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1)
      hph.cls (hnr stCls_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case j1 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bJ1 rfl stJ1_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j1
      (hnr stJ1_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case d0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_pre hI bD0 bD1 rfl (hC _ fun _ _ hJ => hJ.1) (hsi _ (by simp [siPcs])) (hsi _ (by simp [siPcs]))
      (hT _ (by simp [takePcs, siPcs])) (hT _ (by simp [takePcs, siPcs]))
  case d2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bD2 rfl stFreeN_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.d2
      (hnr stFreeN_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case d7 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_pre hI bD7 bD8 rfl (hC _ fun _ _ hJ => hJ.1) (hsi _ (by simp [siPcs])) (hsi _ (by simp [siPcs]))
      (hT _ (by simp [takePcs, siPcs])) (hT _ (by simp [takePcs, siPcs]))
  case d9 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bD9 rfl stFree_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.d9
      (hnr stFree_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case d14 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_pre hI bD14 bD15 rfl (hC _ fun _ _ hJ => hJ.1) (hsi _ (by simp [siPcs]))
      (hsi _ (by simp [siPcs])) (hT _ (by simp [takePcs, siPcs])) (hT _ (by simp [takePcs, siPcs]))
  case d16 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bD16 rfl stLock_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.d16
      (hnr stLock_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case sp0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bSp0 (ofNat4_zero _) stSwp_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1)
      hph.sp0 (hnr stSwp_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case swp =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_swp_pre hI hown bSwp rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.swpOk (hT _ (by simp [takePcs]))
      (hT _ (by simp [takePcs])) (fun _ _ hJ => hJ.2.2.2) hmL hunL hph.swpIn fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.swpUpd
  case sp3 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bSp3 rfl stSpin_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.sp3
      (hnr stSpin_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case lk0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bLk0 (ofNat4_zero _) stLdN_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1)
      hph.lk0 (hnr stLdN_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case ldn =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact nodeW_ldr_pre hI bLdn rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.ldnOk (hT _ (by simp [takePcs])) hph.ldnPh
      (fun σ _ hJ => by rw [Tcb.rAddr_zero]; exact hJ.2.2) hmN hunN
  case lk2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bLk2 rfl stEmpty_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.lk2
      (hnr stEmpty_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case b0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_pre hI bB0 bB1 rfl (hC _ fun _ _ hJ => hJ.1) (hsi _ (by simp [siPcs])) (hsi _ (by simp [siPcs]))
      (hT _ (by simp [takePcs, siPcs])) (hT _ (by simp [takePcs, siPcs]))
  case b2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bB2 rfl stUnl_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.b2
      (hnr stUnl_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case unl =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_stlr_pre hI hown bUnl rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.unlOk (hT _ (by simp [takePcs]))
      (hT _ (by simp [takePcs])) (fun σ _ hJ => hJ.2.2.2) hmL hunL hph.unlIn fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.unlUpd
  case b6 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_pre hI bB6 bB7 rfl (hC _ fun _ _ hJ => hJ.1) (hsi _ (by simp [siPcs])) (hsi _ (by simp [siPcs]))
      (hT _ (by simp [takePcs, siPcs])) (hT _ (by simp [takePcs, siPcs]))
  case b8 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bB8 rfl stAdd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.b8
      (hnr stAdd_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case nxt =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_ldop_pre hI hown bNxt rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.nxtOk (hT _ (by simp [takePcs]))
      (hT _ (by simp [takePcs])) (fun σ _ hJ => hJ.2.2.2) hmX hunX hph.nxtIn fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.nxtUpd
  case b12 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bB12 rfl stBnd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.b12
      (hnr stBnd_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case b21 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bB21 rfl stJ2_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.b21
      (hnr stJ2_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case ok0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_pre hI bOk0 bOk1 rfl (hC _ fun _ _ hJ => hJ.1) (hsi _ (by simp [siPcs]))
      (hsi _ (by simp [siPcs])) (hT _ (by simp [takePcs, siPcs])) (hT _ (by simp [takePcs, siPcs]))
  case ok2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bOk2 rfl stOk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok2
      (hnr stOk_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case tk =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_pre hI bTk (ofNat4_zero _) stSite_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1)
      hph.tk (hnr stSite_noRet) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))
  case site =>
    dsimp only [TakeW]
    rw [hI.labOk]
    rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hc, -, h0, h1⟩
    have hcl := cellOf hI (d := .instr ⟨.W64, .NOP⟩) bSite (ofNat4_zero _) hs hn hpc
    have hpc' : s.st.2 = lab siteL := hpc
    have hpcN : pcOf s = (lab siteL).toBitVec.toNat := by unfold pcOf; rw [hpc']
    have hpc4 : ∀ m, (Kraken.Promising.Lower.A64.after s 4 m).st.2 = lab siteL + Int64.ofNat 4 := fun _ => by
      show s.st.2 + Int64.ofNat 4 = _; rw [hpc']
    refine sfacts_site (hc ▸ hq ▸ hC0) (fun a ha => by rw [hpcN]; exact hph.siteRel a ha)
      (fun k a ha => by rw [hpcN]; exact hph.siteAb k a ha) hcl
      (hT (lab siteL + Int64.ofNat (4 * 0)) (by simp [takePcs]) s (by rw [hpcN, ofNat4_zero]))
      ⟨?_, hsub, by rw [hrS]; exact Nat.succ_pos _, hdisj⟩
      (fun m => by rw [own_at hown (hpc4 m), own_at hown hpc']; exact hph.siteOwn) (fun m => ?_)
      (by rw [hpcN]; exact hph.siteAt)
    · show (⟨s.st.1.regs.X0.toBitVec.toNat, s.st.1.regs.X1.toBitVec.toNat⟩ : Range) = rS
      rw [hA.regs, h0, h1, hrS]; rfl
    · refine hph.tk4 _ ?_
      show (Scc.Sem.A64.nextPc (Scc.Sem.A64.abi.setDmem s m)).toBitVec.toNat = _
      rw [Scc.Sem.A64.nextPc_of_cellAt (st := Scc.Sem.A64.abi.setDmem s m) ⟨hcl.valid, hcl.ne, hcl.code⟩]
      show (s.st.2 + Int64.ofNat 4).toBitVec.toNat = _
      rw [hpc']
  case ret =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_post hI bRet rfl stRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.2.1) hph.ret
      (hret_of_run stRet_ok fun _ _ hJ => by
        dsimp only [takeNG] at hJ ⊢
        rw [(stRet_walk lab _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Spike.Lib.A64.Rt
