/-
**`scc_rt_stack_take`'s states inside `W` on x86-64, for any program**
(`takeW_gen`): the obligations `TakeW` (`Spike/Lib/X64Ret0.lean`) of every
node of `scc_rt_stack_take`'s feasible path, from an instance's facts
(`InstOk`), the function's code (`stackTakeIn`, a field of the runtime's
code checks), its phase facts (`TakePh`), the three words it accesses and
the range it takes. The twin of `Spike/Lib/Rt/A64RtTake.lean`.

- **The phase facts** (`TakePh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), no dead target; each `leaq` off
  the sites in its next pc's phase (`siPcs`); no node before the site in the
  take's phase; the lock `scc_rt_stack_lock` owned at its `xchg` and its
  release and set by them, `scc_rt_stack_next` owned at its `lock xadd` and
  updated by it, the free count's load in its next pc's phase.
- **The take site** (the `nop` row, skipped by `RtNodesOk`): off the release
  and abort sites, the marks' take site, its next pc in the take's phase
  with the same owned words; the range named by `%rdi`/`%rsi` in the pool
  (`hrS`, `hsub`), the read-only data off the pool (`hdisj`).
- **The words**: `scc_rt_stack_lock`, `scc_rt_stack_next` (written) and
  `scc_rt_stack_free_n` (read) mapped in the loaded kernel state and
  unmapped in private memory under the frame condition.
- **Oracle**: `ret0.x`'s `takeSiteW` and `takeW` (`Spike/Lib/X64Ret0I.lean`)
  are this at its instance (`Spike/Test/X64RtTake.lean`).
-/
import Spike.Lib.Rt.X64RtTcb

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW takeNG lockA freeNA nextA stacksA StackM swpBlk_eq ldnBlk_eq
  unlBlk_eq nxtBlk_eq)
open Scc.Cert.Rt.X64 (blockAtB)

namespace Take

open Spike.Lib.X64.Flow.Ret0.StackTake

open Kraken.X64.Parser in
/-- The take site's `nop`. -/
theorem nopBlk_eq : ((parse("nop")).zip [1] : List (Directive × Nat)) =
    [(Kraken.Promising.Lower.X64.op64 (.nop 1), 1)] := by
  decide

/-- The pcs of the `leaq`s: `scc_rt_stack_free_n`, `scc_rt_stack_free`,
`scc_rt_stack_lock` (twice), `scc_rt_stack_next` and `scc_rt_stacks`. -/
def siPcs (lab : Label → Int64) : List Int64 :=
  [lab doneL + Int64.ofNat 0, lab doneL + Int64.ofNat 26, lab doneL + Int64.ofNat 52,
    lab bumpL + Int64.ofNat 0, lab bumpL + Int64.ofNat 31, lab okL + Int64.ofNat 0]

/-- The pcs before the take: the nodes' up to the site, and the pcs after
the swap, the release and the add. -/
def takePcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat 0, lab entryL + Int64.ofNat 0, lab clsL + Int64.ofNat 0, lab clsL + Int64.ofNat 13,
    lab doneL + Int64.ofNat 7, lab doneL + Int64.ofNat 33, lab doneL + Int64.ofNat 59,
    lab spinL + Int64.ofNat 0, swpPc lab, swpPc lab + Int64.ofNat 3, lab spinL + Int64.ofNat 14,
    lab lockedL + Int64.ofNat 0, freeNPc lab, lab lockedL + Int64.ofNat 7,
    lab bumpL + Int64.ofNat 7, unlPc lab, unlPc lab + Int64.ofNat 3, lab bumpL + Int64.ofNat 38,
    nextPc lab, nextPc lab + Int64.ofNat 5, lab bumpL + Int64.ofNat 61, lab bumpL + Int64.ofNat 108,
    lab okL + Int64.ofNat 7, lab takenL + Int64.ofNat 0, lab siteL] ++ siPcs lab

/-- **`scc_rt_stack_take`'s phase facts** at labels `lab`, phase index `ph`,
off-site pcs `okPc`, owned words by phase `ownOf`, marks `μ`, returning to
`ra siteL`. -/
structure TakePh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (μ : Marks) (lab ra : Label → Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat 0) (ra fnL) stPro = true
  entry : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 0) (ra entryL) stInit = true
  cls : blkPh okPc ph (fun _ => false) lab (lab clsL + Int64.ofNat 0) (ra clsL) stCls = true
  j1 : blkPh okPc ph (fun _ => false) lab (lab clsL + Int64.ofNat 13) (ra clsL) stJ1 = true
  d7 : blkPh okPc ph (fun _ => false) lab (lab doneL + Int64.ofNat 7) (ra doneL) stFreeN = true
  d33 : blkPh okPc ph (fun _ => false) lab (lab doneL + Int64.ofNat 33) (ra doneL) stFree = true
  d59 : blkPh okPc ph (fun _ => false) lab (lab doneL + Int64.ofNat 59) (ra doneL) stLock = true
  sp0 : blkPh okPc ph (fun _ => false) lab (lab spinL + Int64.ofNat 0) (ra spinL) stSwp = true
  sp14 : blkPh okPc ph (fun _ => false) lab (lab spinL + Int64.ofNat 14) (ra spinL) stSpin = true
  lk0 : blkPh okPc ph (fun _ => false) lab (lab lockedL + Int64.ofNat 0) (ra lockedL) stLdN = true
  lk7 : blkPh okPc ph (fun _ => false) lab (lab lockedL + Int64.ofNat 7) (ra lockedL) stEmpty = true
  b7 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat 7) (ra bumpL) stUnl = true
  b38 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat 38) (ra bumpL) stAdd = true
  b61 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat 61) (ra bumpL) stBnd = true
  b108 : blkPh okPc ph (fun _ => false) lab (lab bumpL + Int64.ofNat 108) (ra bumpL) stJ2 = true
  ok7 : blkPh okPc ph (fun _ => false) lab (lab okL + Int64.ofNat 7) (ra okL) stOk = true
  tk : blkPh okPc ph (fun _ => false) lab (lab takenL + Int64.ofNat 0) (ra takenL) stSite = true
  ret : blkPh okPc ph (fun _ => false) lab (lab siteL + Int64.ofNat 1) (ra siteL) stRet = true
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 7).toBitVec.toNat = ph p.toBitVec.toNat
  swpOk : okPc (swpPc lab).toBitVec.toNat = true
  ldnOk : okPc (freeNPc lab).toBitVec.toNat = true
  unlOk : okPc (unlPc lab).toBitVec.toNat = true
  nxtOk : okPc (nextPc lab).toBitVec.toNat = true
  ldnPh : ph (freeNPc lab + Int64.ofNat 3).toBitVec.toNat = ph (freeNPc lab).toBitVec.toNat
  noTk : ∀ p ∈ takePcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  swpIn : ∃ v, (⟨lockA lab, 8⟩, v) ∈ ownOf (ph (swpPc lab).toBitVec.toNat)
  swpUpd : ownUpdB (ownOf (ph (swpPc lab).toBitVec.toNat)) (ownOf (ph (swpPc lab + Int64.ofNat 3).toBitVec.toNat))
    ⟨lockA lab, 8⟩ (fun _ => (1#64 : BitVec 64).setWidth 128) = true
  unlIn : ∃ v, (⟨lockA lab, 8⟩, v) ∈ ownOf (ph (unlPc lab).toBitVec.toNat)
  unlUpd : ownUpdB (ownOf (ph (unlPc lab).toBitVec.toNat)) (ownOf (ph (unlPc lab + Int64.ofNat 3).toBitVec.toNat))
    ⟨lockA lab, 8⟩ (fun _ => (0#64 : BitVec 64).setWidth 128) = true
  nxtIn : ∃ v, (⟨nextA lab, 8⟩, v) ∈ ownOf (ph (nextPc lab).toBitVec.toNat)
  nxtUpd : ownUpdB (ownOf (ph (nextPc lab).toBitVec.toNat)) (ownOf (ph (nextPc lab + Int64.ofNat 5).toBitVec.toNat))
    ⟨nextA lab, 8⟩ (fun old => (old.setWidth 64 + size0).setWidth 128) = true
  siteRel : ∀ a, μ.site .release = some a → (lab siteL).toBitVec.toNat ≠ a
  siteAb : ∀ k a, μ.abortAt k = some a → (lab siteL).toBitVec.toNat ≠ a
  siteAt : μ.site .take = some (lab siteL).toBitVec.toNat
  siteOwn : ownOf (ph (lab siteL + Int64.ofNat 1).toBitVec.toNat) = ownOf (ph (lab siteL).toBitVec.toNat)
  tk1 : ∀ s : State, pcOf s = (lab siteL + Int64.ofNat 1).toBitVec.toNat → Tk s

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

set_option hygiene false in
/-- A block of `scc_rt_stack_take` before the take, no `ret`, no dead
target: its code, cover, phase field and no-`ret` lemma. -/
local macro "kblk " ok:term:max f:term:max nr:term:max : tactic =>
  `(tactic| (
    dsimp only [TakeW]
    rw [hI.labOk]
    exact blkW_pre hI (by assumption) (by first | rfl | exact ofNat_zero' _) $ok hR hlo hhi
      (hC _ fun _ _ hJ => hJ.1) $f (hnr $nr) (fun _ _ _ => rfl) (hT _ (by simp [takePcs]))))

set_option hygiene false in
/-- A `leaq L(%rip), %rax` of `scc_rt_stack_take` at `l + off`. -/
local macro "ksi " l:term:max off:term:max : tactic =>
  `(tactic| (
    dsimp only [TakeW]
    rw [hI.labOk]
    have hs := hsi (lab $l + Int64.ofNat $off) (by simp [siPcs])
    exact nodeW_si_pre (p := lab $l + Int64.ofNat $off) hI (by assumption) rfl
      (by first | rfl | exact (ofNat_zero' _).symm) (hC _ fun _ _ hJ => hJ.1) hs.1
      (hT _ (by simp [takePcs, siPcs])) hs.2))

set_option maxHeartbeats 800000 in
open Take Spike.Lib.X64.Flow.Ret0.StackTake in
/-- **`scc_rt_stack_take`'s states are inside `SFacts`**, for any program
with the function's code (`hin`), in any region holding its frame, with the
source control `c0` (`hC0`, its facts), returning to `ra siteL` (`hra`), its
phase facts (`hph`), its three words mapped (`hmL`, `hmN`, `hmX`) and
unmapped in private memory under the frame condition (`hunL`, `hunN`,
`hunX`), the range taken named by the site's registers (`hrS`) in the pool
(`hsub`), off the read-only data (`hdisj`) and kept by the region's writes
(`hSM`). -/
theorem takeW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : stackTakeIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi) (q : TakeG)
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
  simp only [stackTakeIn, Spike.Lib.X64.Flow.Ret0.AllocTcb.siAt, swpBlk_eq, ldnBlk_eq, unlBlk_eq, nxtBlk_eq, nopBlk_eq,
    Bool.and_eq_true] at h
  repeat (obtain ⟨h, _⟩ := h)
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ takePcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 7).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnr : ∀ {blk : List (Directive × Nat)}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
    fun hb _ _ _ _ _ k hk hr => (noRet_false hb k hk hr).elim
  intro i
  cases i
  case e => kblk stPro_ok hph.e stPro_noRet
  case entry => kblk stInit_ok hph.entry stInit_noRet
  case cls => kblk stCls_ok hph.cls stCls_noRet
  case j1 => kblk stJ1_ok hph.j1 stJ1_noRet
  case d0 => ksi doneL 0
  case d7 => kblk stFreeN_ok hph.d7 stFreeN_noRet
  case d26 => ksi doneL 26
  case d33 => kblk stFree_ok hph.d33 stFree_noRet
  case d52 => ksi doneL 52
  case d59 => kblk stLock_ok hph.d59 stLock_noRet
  case sp0 => kblk stSwp_ok hph.sp0 stSwp_noRet
  case swp =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_xchg_pre (p := swpPc lab) hI hown (by assumption) rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.swpOk
      (hT _ (by simp [takePcs])) (hT _ (by simp [takePcs])) (fun σ _ hJ => ?_) hmL hunL hph.swpIn
      fun σ _ hJ => ?_
    · simp [bAddr, Reg64s.get64, hJ.2.2.1]
    · have he : σ.regs.get64 .rax = 1#64 := by rw [← hJ.2.2.2]; rfl
      rw [he]
      exact hph.swpUpd
  case sp14 => kblk stSpin_ok hph.sp14 stSpin_noRet
  case lk0 => kblk stLdN_ok hph.lk0 stLdN_noRet
  case ldn =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_ld_pre (p := freeNPc lab) hI (by assumption) rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.ldnOk
      (hT _ (by simp [takePcs])) hph.ldnPh (fun σ _ hJ => ?_) hmN hunN
    simp [bAddr, Reg64s.get64, hJ.2.2]
  case lk7 => kblk stEmpty_ok hph.lk7 stEmpty_noRet
  case b0 => ksi bumpL 0
  case b7 => kblk stUnl_ok hph.b7 stUnl_noRet
  case unl =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_stown_pre (p := unlPc lab) hI hown (by assumption) rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.unlOk
      (hT _ (by simp [takePcs])) (hT _ (by simp [takePcs])) (fun σ _ hJ => ?_) hmL hunL hph.unlIn
      fun σ _ hJ => ?_
    · simp [bAddr, Reg64s.get64, hJ.2.2.1]
    · have he : σ.regs.get64 .rax = 0#64 := by rw [← hJ.2.2.2]; rfl
      rw [he]
      exact hph.unlUpd
  case b31 => ksi bumpL 31
  case b38 => kblk stAdd_ok hph.b38 stAdd_noRet
  case nxt =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_xadd_pre (p := nextPc lab) hI hown (by assumption) rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.nxtOk
      (hT _ (by simp [takePcs])) (hT _ (by simp [takePcs])) (fun σ _ hJ => ?_) hmX hunX hph.nxtIn
      fun σ _ hJ => ?_
    · simp [bAddr, Reg64s.get64, hJ.2.2.1]
    · have he : σ.regs.get64 .rax = size0 := by rw [← hJ.2.2.2]; rfl
      rw [he]
      exact hph.nxtUpd
  case b61 => kblk stBnd_ok hph.b61 stBnd_noRet
  case b108 => kblk stJ2_ok hph.b108 stJ2_noRet
  case ok0 => ksi okL 0
  case ok7 => kblk stOk_ok hph.ok7 stOk_noRet
  case tk => kblk stSite_ok hph.tk stSite_noRet
  case site =>
    dsimp only [TakeW]
    rw [hI.labOk]
    rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hc, -, h0, h1⟩
    have hpc' : s.st.2 = lab siteL := hpc
    have hcl := cellOf hI (l := siteL) (off := 0) (d := Kraken.Promising.Lower.X64.op64 (.nop 1)) (z := 1)
      (by assumption) (ofNat_zero' _) hs hn hpc'
    have hpcN : pcOf s = (lab siteL).toBitVec.toNat := by unfold pcOf; rw [hpc']
    have hpc1 : ∀ m, (Kraken.Promising.Lower.X64.after s 1 m).st.2 = lab siteL + Int64.ofNat 1 := fun _ => by
      show s.st.2 + Int64.ofNat 1 = _; rw [hpc']
    refine sfacts_site (hc ▸ hq ▸ hC0) (fun a ha => by rw [hpcN]; exact hph.siteRel a ha)
      (fun k a ha => by rw [hpcN]; exact hph.siteAb k a ha) hcl
      (hT (lab siteL) (by simp [takePcs]) s hpcN)
      ⟨?_, hsub, by rw [hrS]; exact Nat.succ_pos _, hdisj⟩
      (fun m => by rw [own_at hown (hpc1 m), own_at hown hpc']; exact hph.siteOwn) (fun m => ?_)
      (by rw [hpcN]; exact hph.siteAt)
    · show (⟨s.st.1.regs.rdi.toBitVec.toNat, s.st.1.regs.rsi.toBitVec.toNat⟩ : Range) = rS
      rw [hA.regs, h0, h1, hrS]; rfl
    · refine hph.tk1 _ ?_
      show (Scc.Sem.X64.nextPc (Scc.Sem.X64.abi.setDmem s m)).toBitVec.toNat = _
      rw [Scc.Sem.X64.nextPc_of_cellAt (st := Scc.Sem.X64.abi.setDmem s m) ⟨hcl.valid, hcl.ne, hcl.code⟩]
      show (s.st.2 + Int64.ofNat 1).toBitVec.toNat = _
      rw [hpc']
  case ret =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_post hI (by assumption) rfl stRet_ok hR hlo hhi (hC _ fun _ _ hJ => hJ.2.1) hph.ret
      (hret_of_run stRet_ok fun _ _ hJ => by
        dsimp only [takeNG] at hJ ⊢
        rw [(stRet_walk lab _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Spike.Lib.X64.Rt
