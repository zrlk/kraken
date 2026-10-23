/-
**`scc_rt_alloc_tcb`'s states inside `W`, for any program** (`tcbW_gen`):
the obligations `TcbW` (`Spike/Lib/A64Ret0.lean`) of every node of
`scc_rt_alloc_tcb`'s feasible path, from an instance's facts (`InstOk`),
the function's code (`allocTcbIn`, a field of `RtCodeIn`), its phase facts
(`TcbPh`) and the two words it writes.

- **The phase facts** (`TcbPh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), its one dead target the abort
  branch's (`tcbDead`); each single instruction off the sites in its next
  pc's phase; no node in the take's phase; the counter
  `scc_rt_pinned_next` owned at its add and updated by it, the header's
  word owned at no phase.
- **The words**: `scc_rt_pinned_next` and the header's word
  `scc_rt_pinned + n0` mapped in the loaded kernel state and unmapped in
  private memory under the frame condition.
- **Oracle**: `ret0.w`'s `tcbW` (`Spike/Lib/A64Ret0I.lean`) is this at its
  instance (`Spike/Test/A64RtTcb.lean`).
-/
import Spike.Lib.Rt.A64RtW

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TN TcbG TcbW tcbN pnA pinA)
open Scc.Cert.Rt.A64 (blockAt)

namespace Tcb

open Spike.Lib.A64.Flow.Ret0.AllocTcb

/-- **The abort branch is the one dead target**: `.0_entry`'s check's
branch to `.2_full`, off the feasible path. -/
def tcbDead (lab : Label → Int64) (l : Label) (k : Nat) (t : Nat) : Bool :=
  l == entryL && k == 0 && t == (lab fullL).toBitVec.toNat

/-- The pcs of the single instructions without an event, and the header's
store: the two label pairs' and `.3_ok`'s store. -/
def siPcs (lab : Label → Int64) : List Int64 :=
  [lab lenL + Int64.ofNat (4 * 32), lab lenL + Int64.ofNat (4 * 33), lab okL + Int64.ofNat (4 * 0),
    lab okL + Int64.ofNat (4 * 1), lab okL + Int64.ofNat (4 * 29)]

/-- The nodes' pcs and the pc after the counter's add. -/
def tcbPcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat (4 * 0), lab entryL + Int64.ofNat (4 * 0), lab entryL + Int64.ofNat (4 * 4),
    lab lenL + Int64.ofNat (4 * 0), lab lenL + Int64.ofNat (4 * 34), rmwPc lab, rmwPc lab + Int64.ofNat 4,
    lab lenL + Int64.ofNat (4 * 38), lab lenL + Int64.ofNat (4 * 47), lab okL + Int64.ofNat (4 * 2),
    lab okL + Int64.ofNat (4 * 30)] ++ siPcs lab

/-- **`scc_rt_alloc_tcb`'s phase facts** at labels `lab`, phase index `ph`,
off-site pcs `okPc`, owned words by phase `ownOf`, returning to `ra okL`,
the header at `scc_rt_pinned + n0`. -/
structure TcbPh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab ra : Label → Int64) (n0 : BitVec 64) : Prop where
  e : blkPh okPc ph (tcbDead lab fnL 0) lab (lab fnL + Int64.ofNat (4 * 0)) (ra fnL) atPro = true
  entry : blkPh okPc ph (tcbDead lab entryL 0) lab (lab entryL + Int64.ofNat (4 * 0)) (ra entryL) atChk = true
  j1 : blkPh okPc ph (tcbDead lab entryL 4) lab (lab entryL + Int64.ofNat (4 * 4)) (ra entryL) atJ1 = true
  len : blkPh okPc ph (tcbDead lab lenL 0) lab (lab lenL + Int64.ofNat (4 * 0)) (ra lenL) atLen = true
  arg : blkPh okPc ph (tcbDead lab lenL 34) lab (lab lenL + Int64.ofNat (4 * 34)) (ra lenL) atArg = true
  bnd : blkPh okPc ph (tcbDead lab lenL 38) lab (lab lenL + Int64.ofNat (4 * 38)) (ra lenL) atBnd = true
  j2 : blkPh okPc ph (tcbDead lab lenL 47) lab (lab lenL + Int64.ofNat (4 * 47)) (ra lenL) atJ2 = true
  ok2 : blkPh okPc ph (tcbDead lab okL 2) lab (lab okL + Int64.ofNat (4 * 2)) (ra okL) atOk = true
  ret : blkPh okPc ph (tcbDead lab okL 30) lab (lab okL + Int64.ofNat (4 * 30)) (ra okL) atRet = true
  fullNe : (lab entryL + Int64.ofNat (4 * 4)).toBitVec.toNat ≠ (lab fullL).toBitVec.toNat
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  noTk : ∀ p ∈ tcbPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  rmwIn : ∃ v, (⟨pnA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨pnA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) tcbLen).setWidth 128) = true
  hdrNo : ∀ j w, (⟨pinA lab + n0, 8⟩, w) ∉ ownOf j

/-- An address with offset `0` is the base register's. -/
theorem rAddr_zero (r : Reg64s) (b : XReg) : Spike.Lib.A64.Flow.rAddr r b 0 = (r.getXReg b).toBitVec := by
  simp [Spike.Lib.A64.Flow.rAddr]

theorem atPro_noRet : noRetBlk atPro = true := by rfl
theorem atChk_noRet : noRetBlk atChk = true := by rfl
theorem atJ1_noRet : noRetBlk atJ1 = true := by rfl
theorem atLen_noRet : noRetBlk atLen = true := by rfl
theorem atArg_noRet : noRetBlk atArg = true := by rfl
theorem atBnd_noRet : noRetBlk atBnd = true := by rfl
theorem atJ2_noRet : noRetBlk atJ2 = true := by rfl
theorem atOk_noRet : noRetBlk atOk = true := by rfl

end Tcb

open Tcb Spike.Lib.A64.Flow.Ret0.AllocTcb in
/-- **`scc_rt_alloc_tcb`'s states are inside `SFacts`**, for any program
with the function's code (`hin`), in any region holding its frame, with the
source control `c0` (`hC0`, its facts), returning to `ra okL` (`hra`), its
phase facts (`hph`) and its two words mapped (`hmP`, `hmH`) and unmapped in
private memory under the frame condition (`hunP`, `hunH`). -/
theorem tcbW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : allocTcbIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) (q : TcbG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hph : TcbPh okPc ph Tk ownOf lab ra q.n0)
    (hmP : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pnA lab, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pinA lab + q.n0, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (pnA lab) 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (pinA lab + q.n0) 8 = none) :
    ∀ i, TcbW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F q i := by
  have h := hin
  simp only [allocTcbIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ tcbPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnr : ∀ {blk : List Directive}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim
  intro i
  cases i
  case e =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bE (ofNat4_zero _) atPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr atPro_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case entry =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bEn (ofNat4_zero _) atChk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.entry
      (hnr atChk_noRet)
      (fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(atChk_walk lab _ hJ.2).1]
        simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
        exact hph.fullNe)
      (hT _ (by simp [tcbPcs]))
  case j1 =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bJ1 rfl atJ1_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j1
      (hnr atJ1_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case len =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bLen (ofNat4_zero _) atLen_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.len
      (hnr atLen_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case adrp =>
    dsimp only [TcbW]; rw [hI.labOk]
    have := hsi (lab lenL + Int64.ofNat (4 * 32)) (by simp [siPcs])
    exact nodeW_si_pre hI bA rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs])) this.2
  case add =>
    dsimp only [TcbW]; rw [hI.labOk]
    have := hsi (lab lenL + Int64.ofNat (4 * 33)) (by simp [siPcs])
    exact nodeW_si_pre hI bA1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs])) this.2
  case arg =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bArg rfl atArg_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr atArg_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case rmw =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine nodeW_ldop_pre hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk (hT _ (by simp [tcbPcs]))
      (hT _ (by simp [tcbPcs])) (fun σ _ hJ => hJ.2.2.2) hmP hunP hph.rmwIn fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.rmwUpd
  case bnd =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bBnd rfl atBnd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr atBnd_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case j2 =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bJ2 rfl atJ2_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j2
      (hnr atJ2_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case ok =>
    dsimp only [TcbW]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 0)) (by simp [siPcs])
    exact nodeW_si_pre hI bO rfl (ofNat4_zero _).symm (hC _ fun _ _ hJ => hJ.1) this.1
      (hT _ (by simp [tcbPcs, siPcs])) this.2
  case ok1 =>
    dsimp only [TcbW]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 1)) (by simp [siPcs])
    exact nodeW_si_pre hI bO1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs])) this.2
  case ok2 =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bO2 rfl atOk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok2
      (hnr atOk_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case hdr =>
    dsimp only [TcbW]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 29)) (by simp [siPcs])
    refine nodeW_st_pre hI hown bH rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs]))
      this.2 (fun σ _ hJ => ?_) hmH hunH hph.hdrNo
    rw [rAddr_zero]
    exact hJ.2.2.2
  case ret =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_pre hI bRet rfl atRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(atRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))

end Spike.Lib.A64.Rt
