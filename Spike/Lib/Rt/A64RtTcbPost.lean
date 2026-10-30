/-
**`scc_rt_alloc_tcb` inside `W` after the take, at a header `h`** (AArch64):
the node obligations `TcbWG` (`Spike/Lib/Rt/A64RtTcbG.lean`) of an
`scc_rt_alloc_tcb` called once the caller's stack range `rS` is taken (its
nodes in the take's phase, the frame condition carrying `StackM rS`), as
`Spike/Lib/Rt/A64RtReservePost.lean` for the reserve.

Per-call phase projection; generic multi-spawn wants a reserve/post-take
phase bit (trusted, cleanup list).

- `TcbPhGP`: `TcbPhG` without `noTk`, the take's phase kept across the
  counter's add (`rmwTk`); `TcbPhGP.of_tcbPhG` from `TcbPhG` at the empty
  take's phase.
- `tcbW_postG`: the node obligations from them, as `tcbW_genG`.
-/
import Spike.Lib.Rt.A64RtTcbG
import Spike.Lib.Rt.A64RtReservePost

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer

set_option linter.unusedSimpArgs false

namespace Tcb

open Spike.Lib.A64.Flow.Ret0.AllocTcb

/-- **`scc_rt_alloc_tcb`'s phase facts after the take** at header `h`: as
`TcbPhG`, without `noTk`, every state at the add in the take's phase iff its
successors are (`rmwTk`). -/
structure TcbPhGP (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab ra : Label → Int64) (h n0 : BitVec 64) : Prop where
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
  rmwTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 4 m) ↔ Tk s
  rmwIn : ∃ v, (⟨pnA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨pnA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) (lenOf h)).setWidth 128) = true
  hdrNo : ∀ j w, (⟨pinA lab + n0 + mOf h <<< 3, 8⟩, w) ∉ ownOf j

/-- **`TcbPhGP` from `TcbPhG`** at the empty take's phase, given the add's
`rmwTk`. -/
theorem TcbPhGP.of_tcbPhG {okPc : Nat → Bool} {ph : Nat → Nat} {Tk : State → Prop}
    {ownOf : Nat → List (Loc × Val)} {lab ra : Label → Int64} {h n0 : BitVec 64}
    (H : TcbPhG okPc ph (fun _ => False) ownOf lab ra h n0)
    (hTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 4 m) ↔ Tk s) :
    TcbPhGP okPc ph Tk ownOf lab ra h n0 :=
  ⟨H.e, H.entry, H.j1, H.len, H.arg, H.bnd, H.j2, H.ok2, H.ret, H.fullNe, H.si, H.rmwOk, hTk, H.rmwIn, H.rmwUpd,
    H.hdrNo⟩

/-- **`scc_rt_alloc_tcb`'s states at `h` are inside `SFacts` after the
take**: as `tcbW_genG`, its frame condition also `StackM rS` (kept by the
region's writes, `hSM`), `rS` in the pool (`hsub`), its phase facts
`TcbPhGP`. -/
theorem tcbW_postG {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : allocTcbIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) (q : TcbGG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hph : TcbPhGP okPc ph Tk ownOf lab ra q.h q.n0)
    (hmP : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pnA lab, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨hdrA lab q, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (pnA lab) 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (hdrA lab q) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    ∀ i, TcbWG (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) q i := by
  have h := hin
  simp only [allocTcbIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnr : ∀ {blk : List Directive}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim
  intro i
  cases i
  case e =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bE (ofNat4_zero _) atPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr atPro_noRet) (fun _ _ _ => rfl) hsub hSM
  case entry =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bEn (ofNat4_zero _) atChk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.entry
      (hnr atChk_noRet)
      (fun _ _ hJ => by
        dsimp only [tcbNG] at hJ ⊢
        rw [(atChk_walkG lab _ hJ.2).1]
        simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
        exact hph.fullNe)
      hsub hSM
  case j1 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bJ1 rfl atJ1_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j1
      (hnr atJ1_noRet) (fun _ _ _ => rfl) hsub hSM
  case len =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bLen (ofNat4_zero _) atLen_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.len
      (hnr atLen_noRet) (fun _ _ _ => rfl) hsub hSM
  case adrp =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab lenL + Int64.ofNat (4 * 32)) (by simp [siPcs])
    exact nodeW_si_post hI bA rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case add =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab lenL + Int64.ofNat (4 * 33)) (by simp [siPcs])
    exact nodeW_si_post hI bA1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case arg =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bArg rfl atArg_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr atArg_noRet) (fun _ _ _ => rfl) hsub hSM
  case rmw =>
    dsimp only [TcbWG]; rw [hI.labOk]
    refine nodeW_ldop_post hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk hph.rmwTk
      (fun σ _ hJ => hJ.2.2.2) hmP hunP hph.rmwIn (fun σ _ hJ => ?_) hsub
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.rmwUpd
  case bnd =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bBnd rfl atBnd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr atBnd_noRet) (fun _ _ _ => rfl) hsub hSM
  case j2 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bJ2 rfl atJ2_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j2
      (hnr atJ2_noRet) (fun _ _ _ => rfl) hsub hSM
  case ok =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 0)) (by simp [siPcs])
    exact nodeW_si_post hI bO rfl (ofNat4_zero _).symm (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case ok1 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 1)) (by simp [siPcs])
    exact nodeW_si_post hI bO1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case ok2 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bO2 rfl atOk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok2
      (hnr atOk_noRet) (fun _ _ _ => rfl) hsub hSM
  case hdr =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 29)) (by simp [siPcs])
    refine nodeW_st_post hI hown bH rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1
      this.2 (fun σ _ hJ => ?_) hmH hunH hph.hdrNo hsub
    rw [rAddr_zero]
    exact hJ.2.2.2
  case ret =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI bRet rfl atRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbNG] at hJ ⊢
        rw [(atRet_walkG lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

/-- info: 'Spike.Lib.A64.Rt.Tcb.tcbW_postG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcbW_postG

end Tcb

end Spike.Lib.A64.Rt
