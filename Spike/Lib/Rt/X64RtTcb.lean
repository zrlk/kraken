/-
**`scc_rt_alloc_tcb`'s states inside `W` on x86-64, for any program**
(`tcbW_gen`): the obligations `TcbW` (`Spike/Lib/X64Ret0.lean`) of every
node of `scc_rt_alloc_tcb`'s feasible path, from an instance's facts
(`InstOk`), the function's code (`allocTcbIn`, a field of the runtime's code
checks), its phase facts (`TcbPh`) and the two words it writes. The twin of
`Spike/Lib/Rt/A64RtTcb.lean`.

- **The phase facts** (`TcbPh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6; a field per block, the row's index
  `k` and byte offset), its one dead target the abort branch's (`tcbDead`);
  each single instruction (`leaq`, the flag-clobbering ones, the header's
  store) off the sites and in its next pc's phase (`stepPcs`); no node in
  the take's phase; the counter `scc_rt_pinned_next` owned at its
  `lock xadd` and updated by it, the header's word owned at no phase.
- **The words**: `scc_rt_pinned_next` and the header's word
  `scc_rt_pinned + n0` mapped in the loaded kernel state and unmapped in
  private memory under the frame condition.
- **Oracle**: `ret0.x`'s `tcbW` (`Spike/Lib/X64Ret0I.lean`) is this at its
  instance (`Spike/Test/X64RtTcb.lean`).
-/
import Spike.Lib.Rt.X64RtW

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TN TcbG TcbW tcbN pnA pinA hdrBlk_eq rmwBlk_eq)
open Scc.Cert.Rt.X64 (blockAtB)

namespace Tcb

open Spike.Lib.X64.Flow.Ret0.AllocTcb

/-- **The abort branch is the one dead target**: `.entry`'s check's branch
to `.full` (row `0`), off the feasible path. -/
def tcbDead (lab : Label → Int64) (l : Label) (k : Nat) (t : Nat) : Bool :=
  l == entryL && k == 0 && t == (lab fullL).toBitVec.toNat

/-- The single instructions' pcs and sizes: the length's and the header's
flag-clobbering instructions, the two `leaq`s and the header's store. -/
def stepPcs (lab : Label → Int64) : List (Int64 × Nat) :=
  [(lab lenL + Int64.ofNat 11, 3), (lab lenL + Int64.ofNat 29, 3), (lab lenL + Int64.ofNat 47, 3),
    (lab lenL + Int64.ofNat 65, 3), (lab lenL + Int64.ofNat 95, 4), (lab lenL + Int64.ofNat 132, 3),
    (lab lenL + Int64.ofNat 139, 7), (lab okL + Int64.ofNat 0, 7), (lab okL + Int64.ofNat 34, 4),
    (lab okL + Int64.ofNat 53, 3), (lab okL + Int64.ofNat 74, 3), (lab okL + Int64.ofNat 95, 3),
    (lab okL + Int64.ofNat 140, 3)]

/-- The blocks' pcs. -/
def blkPcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat 0, lab entryL + Int64.ofNat 0, lab entryL + Int64.ofNat 20, lab lenL + Int64.ofNat 0,
    lab lenL + Int64.ofNat 14, lab lenL + Int64.ofNat 32, lab lenL + Int64.ofNat 50, lab lenL + Int64.ofNat 68,
    lab lenL + Int64.ofNat 99, lab lenL + Int64.ofNat 135, lab lenL + Int64.ofNat 146,
    lab lenL + Int64.ofNat 163, lab lenL + Int64.ofNat 198, lab okL + Int64.ofNat 7, lab okL + Int64.ofNat 38,
    lab okL + Int64.ofNat 56, lab okL + Int64.ofNat 77, lab okL + Int64.ofNat 98, lab okL + Int64.ofNat 143]

/-- The nodes' pcs and the pc after the counter's add. -/
def tcbPcs (lab : Label → Int64) : List Int64 :=
  blkPcs lab ++ (stepPcs lab).map (·.1) ++ [rmwPc lab, rmwPc lab + Int64.ofNat 5]

/-- **`scc_rt_alloc_tcb`'s phase facts** at labels `lab`, phase index `ph`,
off-site pcs `okPc`, owned words by phase `ownOf`, returning to `ra okL`,
the header at `scc_rt_pinned + n0`. Each block's field is its row's phase
check (`rowPh` at the row `(l, k, off)`). -/
structure TcbPh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab ra : Label → Int64) (n0 : BitVec 64) : Prop where
  e : blkPh okPc ph (tcbDead lab fnL 0) lab (lab fnL + Int64.ofNat 0) (ra fnL) atPro = true
  entry : blkPh okPc ph (tcbDead lab entryL 0) lab (lab entryL + Int64.ofNat 0) (ra entryL) atChk = true
  j1 : blkPh okPc ph (tcbDead lab entryL 4) lab (lab entryL + Int64.ofNat 20) (ra entryL) atJ1 = true
  len : blkPh okPc ph (tcbDead lab lenL 0) lab (lab lenL + Int64.ofNat 0) (ra lenL) atL0 = true
  l1 : blkPh okPc ph (tcbDead lab lenL 3) lab (lab lenL + Int64.ofNat 14) (ra lenL) atL1 = true
  l2 : blkPh okPc ph (tcbDead lab lenL 7) lab (lab lenL + Int64.ofNat 32) (ra lenL) atL2 = true
  l3 : blkPh okPc ph (tcbDead lab lenL 11) lab (lab lenL + Int64.ofNat 50) (ra lenL) atL3 = true
  l4 : blkPh okPc ph (tcbDead lab lenL 15) lab (lab lenL + Int64.ofNat 68) (ra lenL) atL4 = true
  l5 : blkPh okPc ph (tcbDead lab lenL 23) lab (lab lenL + Int64.ofNat 99) (ra lenL) atL5 = true
  l6 : blkPh okPc ph (tcbDead lab lenL 31) lab (lab lenL + Int64.ofNat 135) (ra lenL) atL6 = true
  arg : blkPh okPc ph (tcbDead lab lenL 33) lab (lab lenL + Int64.ofNat 146) (ra lenL) atArg = true
  bnd : blkPh okPc ph (tcbDead lab lenL 37) lab (lab lenL + Int64.ofNat 163) (ra lenL) atBnd = true
  j2 : blkPh okPc ph (tcbDead lab lenL 46) lab (lab lenL + Int64.ofNat 198) (ra lenL) atJ2 = true
  o1 : blkPh okPc ph (tcbDead lab okL 1) lab (lab okL + Int64.ofNat 7) (ra okL) atO1 = true
  o2 : blkPh okPc ph (tcbDead lab okL 9) lab (lab okL + Int64.ofNat 38) (ra okL) atO2 = true
  o3 : blkPh okPc ph (tcbDead lab okL 13) lab (lab okL + Int64.ofNat 56) (ra okL) atO3 = true
  o4 : blkPh okPc ph (tcbDead lab okL 17) lab (lab okL + Int64.ofNat 77) (ra okL) atO4 = true
  o5 : blkPh okPc ph (tcbDead lab okL 21) lab (lab okL + Int64.ofNat 98) (ra okL) atO5 = true
  ret : blkPh okPc ph (tcbDead lab okL 29) lab (lab okL + Int64.ofNat 143) (ra okL) atRet = true
  fullNe : (lab entryL + Int64.ofNat 20).toBitVec.toNat ≠ (lab fullL).toBitVec.toNat
  step : ∀ pz ∈ stepPcs lab, okPc pz.1.toBitVec.toNat = true ∧
    ph (pz.1 + Int64.ofNat pz.2).toBitVec.toNat = ph pz.1.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  noTk : ∀ p ∈ tcbPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  rmwIn : ∃ v, (⟨pnA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 5).toBitVec.toNat))
    ⟨pnA lab, 8⟩ (fun old => (old.setWidth 64 + tcbLen).setWidth 128) = true
  hdrNo : ∀ j w, (⟨pinA lab + n0, 8⟩, w) ∉ ownOf j

theorem atPro_noRet : noRetBlk atPro = true := by rfl
theorem atChk_noRet : noRetBlk atChk = true := by rfl
theorem atJ1_noRet : noRetBlk atJ1 = true := by rfl
theorem atL0_noRet : noRetBlk atL0 = true := by rfl
theorem atL1_noRet : noRetBlk atL1 = true := by rfl
theorem atL2_noRet : noRetBlk atL2 = true := by rfl
theorem atL3_noRet : noRetBlk atL3 = true := by rfl
theorem atL4_noRet : noRetBlk atL4 = true := by rfl
theorem atL5_noRet : noRetBlk atL5 = true := by rfl
theorem atL6_noRet : noRetBlk atL6 = true := by rfl
theorem atArg_noRet : noRetBlk atArg = true := by rfl
theorem atBnd_noRet : noRetBlk atBnd = true := by rfl
theorem atJ2_noRet : noRetBlk atJ2 = true := by rfl
theorem atO1_noRet : noRetBlk atO1 = true := by rfl
theorem atO2_noRet : noRetBlk atO2 = true := by rfl
theorem atO3_noRet : noRetBlk atO3 = true := by rfl
theorem atO4_noRet : noRetBlk atO4 = true := by rfl
theorem atO5_noRet : noRetBlk atO5 = true := by rfl

end Tcb

set_option hygiene false in
/-- A block of `scc_rt_alloc_tcb` before the take, no `ret`, no dead target
reached: its code, cover, phase field and no-`ret` lemma. -/
local macro "tblk " ok:term:max f:term:max nr:term:max : tactic =>
  `(tactic| (
    dsimp only [TcbW]
    rw [hI.labOk]
    exact blkW_pre hI (by assumption) (by first | rfl | exact ofNat_zero' _) $ok hR hlo hhi
      (hC _ fun _ _ hJ => hJ.1) $f (hnr $nr) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs, blkPcs]))))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc_tcb` without an event (`leaq`, or
one clobbering the flags), at `l + off`. -/
local macro "tstep " lem:ident l:term:max off:term:max z:term:max : tactic =>
  `(tactic| (
    dsimp only [TcbW]
    rw [hI.labOk]
    have hs := hstep (lab $l + Int64.ofNat $off, $z) (by simp [stepPcs])
    exact $lem (p := lab $l + Int64.ofNat $off) hI (by assumption) rfl (by first | rfl | exact (ofNat_zero' _).symm) (hC _ fun _ _ hJ => hJ.1)
      hs.1 (hT _ (by simp [tcbPcs, stepPcs])) hs.2))

open Tcb Spike.Lib.X64.Flow.Ret0.AllocTcb in
/-- **`scc_rt_alloc_tcb`'s states are inside `SFacts`**, for any program
with the function's code (`hin`), in any region holding its frame, with the
source control `c0` (`hC0`, its facts), returning to `ra okL` (`hra`), its
phase facts (`hph`) and its two words mapped (`hmP`, `hmH`) and unmapped in
private memory under the frame condition (`hunP`, `hunH`). -/
theorem tcbW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : allocTcbIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi) (q : TcbG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hph : TcbPh okPc ph Tk ownOf lab ra q.n0)
    (hmP : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pnA lab, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pinA lab + q.n0, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (pnA lab) 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (pinA lab + q.n0) 8 = none) :
    ∀ i, TcbW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F q i := by
  have h := hin
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at h
  repeat (obtain ⟨h, _⟩ := h)
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ tcbPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hstep : ∀ pz ∈ stepPcs lab, okPc pz.1.toBitVec.toNat = true ∧
      ph (pz.1 + Int64.ofNat pz.2).toBitVec.toNat = ph pz.1.toBitVec.toNat := hph.step
  have hnr : ∀ {blk : List (Directive × Nat)}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
    fun hb _ _ _ _ _ k hk hr => (noRet_false hb k hk hr).elim
  intro i
  cases i
  case e => tblk atPro_ok hph.e atPro_noRet
  case entry =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI (by assumption) (ofNat_zero' _) atChk_ok hR hlo hhi (hC _ fun _ _ hJ => hJ.1) hph.entry
      (hnr atChk_noRet)
      (fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(atChk_walk lab _ hJ.2).1]
        simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
        exact hph.fullNe)
      (hT _ (by simp [tcbPcs, blkPcs]))
  case j1 => tblk atJ1_ok hph.j1 atJ1_noRet
  case len => tblk atL0_ok hph.len atL0_noRet
  case shr1 => tstep nodeW_fi_pre lenL 11 3
  case l1 => tblk atL1_ok hph.l1 atL1_noRet
  case and1 => tstep nodeW_fi_pre lenL 29 3
  case l2 => tblk atL2_ok hph.l2 atL2_noRet
  case shr2 => tstep nodeW_fi_pre lenL 47 3
  case l3 => tblk atL3_ok hph.l3 atL3_noRet
  case and2 => tstep nodeW_fi_pre lenL 65 3
  case l4 => tblk atL4_ok hph.l4 atL4_noRet
  case imul1 => tstep nodeW_fi_pre lenL 95 4
  case l5 => tblk atL5_ok hph.l5 atL5_noRet
  case shl1 => tstep nodeW_fi_pre lenL 132 3
  case l6 => tblk atL6_ok hph.l6 atL6_noRet
  case lea1 => tstep nodeW_si_pre lenL 139 7
  case arg => tblk atArg_ok hph.arg atArg_noRet
  case rmw =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine nodeW_xadd_pre (p := rmwPc lab) hI hown (by assumption) (by rfl) rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk
      (hT _ (List.mem_append_right _ (.head _))) (hT _ (List.mem_append_right _ (.tail _ (.head _)))) (fun σ _ hJ => ?_) hmP hunP hph.rmwIn
      fun σ _ hJ => ?_
    · obtain ⟨-, -, -, hc⟩ := hJ
      rw [← hc]
      simp [bAddr, Reg64s.get64]
    · obtain ⟨-, -, ha, -⟩ := hJ
      have he : σ.regs.get64 .rax = tcbLen := by rw [← ha]; rfl
      rw [he]
      exact hph.rmwUpd
  case bnd => tblk atBnd_ok hph.bnd atBnd_noRet
  case j2 => tblk atJ2_ok hph.j2 atJ2_noRet
  case ok => tstep nodeW_si_pre okL 0 7
  case o1 => tblk atO1_ok hph.o1 atO1_noRet
  case imul2 => tstep nodeW_fi_pre okL 34 4
  case o2 => tblk atO2_ok hph.o2 atO2_noRet
  case shl2 => tstep nodeW_fi_pre okL 53 3
  case o3 => tblk atO3_ok hph.o3 atO3_noRet
  case shl3 => tstep nodeW_fi_pre okL 74 3
  case o4 => tblk atO4_ok hph.o4 atO4_noRet
  case or1 => tstep nodeW_fi_pre okL 95 3
  case o5 => tblk atO5_ok hph.o5 atO5_noRet
  case hdr =>
    dsimp only [TcbW]; rw [hI.labOk]
    have hs := hstep (lab okL + Int64.ofNat 140, 3) (by simp [stepPcs])
    refine nodeW_st_pre (p := lab okL + Int64.ofNat 140) hI hown (by assumption) rfl rfl (hC _ fun _ _ hJ => hJ.1) hs.1
      (hT _ (by simp [tcbPcs, stepPcs])) hs.2 (fun σ _ hJ => ?_) hmH hunH hph.hdrNo
    obtain ⟨-, -, -, hc⟩ := hJ
    have he : σ.regs.rcx.toBitVec = pinA lab + q.n0 := hc
    simp [bAddr, Reg64s.get64, he]
  case ret =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI (by assumption) rfl atRet_ok hR hlo hhi (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(atRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs, blkPcs]))

end Spike.Lib.X64.Rt
