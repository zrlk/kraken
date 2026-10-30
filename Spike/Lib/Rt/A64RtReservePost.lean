/-
**`scc_rt_thread_reserve` inside `W` after the take** (AArch64): the node
obligations `ReserveW` (`Spike/Lib/Rt/A64RtReserve.lean`) of a reserve
called once the caller's stack range `rS` is taken, so its nodes are in the
take's phase and the frame condition carries `StackM rS`.

- `nodeW_ldop_post`: an owned word's `ld<op><k>` after the take, the take's
  phase kept across it by a premise on its pc (`hTk`) rather than by the
  phase index (the counter's add may switch phase bits the take's phase
  ignores).
- `ResPhP`: `ResPh` without `noTk`, with the take's phase kept across the
  add (`rmwTk`); `ResPhP.of_resPh` from `ResPh` at the empty phase.
- `reserveW_post`: the node obligations from them, as `reserveW_gen`.
-/
import Spike.Lib.Rt.A64RtReserve

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackM)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt after exec_ldop access_agrees)

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at an owned word's `ld<op><k> Xs, Xt, [Xn]`** after the take,
as `nodeW_ldop_pre`: the word `a` (`ha`), owned at `p` (`hin`), updated at
the next pc (`hupd`); every state at `p` in the take's phase iff its
successors are (`hTk`), the range in private memory (`hsub`). -/
theorem nodeW_ldop_post {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {op : AtomicOp} {kk : RmwKind} {rs rt b : XReg}
    {l : Label} {k : Nat} {p : Int64} {a : BitVec 64} (hb : blockAt prog l k [ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hTk : ∀ s : State, pcOf s = p.toBitVec.toNat → ∀ m, Tk (after s 4 m) ↔ Tk s)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (op.apply (old.setWidth 64) (σ.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128)
      = true) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldop hc (by rw [ha']; exact hun _ hD)
    rw [ha', access_agrees (agrees_of_decls hdc _ _)] at hex
    have hpc4 : ∀ m, (after s 4 m).st.2 = p + Int64.ofNat 4 := fun _ => by rw [← hpc]
    obtain ⟨hT', hown', htk⟩ := rmw_facts (Λ := Λ) (own := own) (Tk := Tk) (s := s) (k := kk)
      (nr := (RegOrZr.low (.reg rt) .W64 : RegOrZr .W64).isZr)
      (op := fun old => some ((op.apply (old.setWidth 64) (s.st.1.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (v.setWidth 64) })
      hmw (fun _ => hTk s (by unfold pcOf; rw [hpc]) _) (by rw [own_at hown hpc]; exact hin)
      (fun v hv => by
        rw [own_at hown hpc, own_at hown (hpc4 _), Option.getD_some, hA.regs]
        rw [own_at hown hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

end Node

namespace Reserve

open Kraken.AArch64.Parser
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Flow.Reserve

/-- **`scc_rt_thread_reserve`'s phase facts after the take**: as `ResPh`,
without `noTk` (its nodes are in the take's phase), every state at the add
in the take's phase iff its successors are (`rmwTk`). -/
structure ResPhP (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab : Label → Int64) (ra : Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat (4 * 0)) ra rPro = true
  arg : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 2)) ra rArg = true
  bnd : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 6)) ra rBnd = true
  j : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 15)) ra rJ = true
  ok : blkPh okPc ph (fun _ => false) lab (lab okL + Int64.ofNat (4 * 0)) ra rRet = true
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  rmwTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 4 m) ↔ Tk s
  rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨ntA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) 1#64).setWidth 128) = true

/-- **The add's `rmwTk` from a take's phase through the phase index**:
`Tk` a predicate `TkW` of the phase, which agrees at the add and past it. -/
theorem rmwTk_of_ph {ph : Nat → Nat} {TkW : Nat → Prop} {lab : Label → Int64}
    (h : TkW (ph (rmwPc lab + Int64.ofNat 4).toBitVec.toNat) ↔ TkW (ph (rmwPc lab).toBitVec.toNat)) :
    ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m,
      TkW (ph (pcOf (after s 4 m))) ↔ TkW (ph (pcOf s)) := by
  intro s hs m
  have he : s.st.2 = rmwPc lab := by
    unfold pcOf at hs
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq hs)
  have h4 : pcOf (after s 4 m) = (rmwPc lab + Int64.ofNat 4).toBitVec.toNat := by
    show (s.st.2 + Int64.ofNat 4).toBitVec.toNat = _; rw [he]
  rw [h4, hs]; exact h

/-- **`ResPhP` from `ResPh`** at the empty take's phase (whose `noTk` is
trivial), given the add's `rmwTk`. -/
theorem ResPhP.of_resPh {okPc : Nat → Bool} {ph : Nat → Nat} {Tk : State → Prop}
    {ownOf : Nat → List (Loc × Val)} {lab : Label → Int64} {ra : Int64}
    (h : ResPh okPc ph (fun _ => False) ownOf lab ra)
    (hTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 4 m) ↔ Tk s) :
    ResPhP okPc ph Tk ownOf lab ra :=
  ⟨h.e, h.arg, h.bnd, h.j, h.ok, h.si, h.rmwOk, hTk, h.rmwIn, h.rmwUpd⟩

/-- **`scc_rt_thread_reserve`'s states are inside `SFacts` after the
take**: as `reserveW_gen`, its frame condition also `StackM rS` (kept by
the region's writes, `hSM`), `rS` in the pool (`hsub`), its phase facts
`ResPhP`. -/
theorem reserveW_post {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : reserveIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (q : ResG)
    (hq : q.c0 = c0) (hra : q.g.ra = ra.toBitVec) (hph : ResPhP okPc ph Tk ownOf lab ra)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨ntA lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA lab) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    ∀ i, ReserveW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) q i := by
  have h := hin
  simp only [reserveIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
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
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bE (ofNat4_zero _) rPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr rPro_noRet) (fun _ _ _ => rfl) hsub hSM
  case entry =>
    dsimp only [ReserveW]; rw [hI.labOk]
    have := hsi (lab entryL + Int64.ofNat (4 * 0)) (by simp [siPcs])
    exact nodeW_si_post hI bA rfl (ofNat4_zero _).symm (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case add =>
    dsimp only [ReserveW]; rw [hI.labOk]
    have := hsi (lab entryL + Int64.ofNat (4 * 1)) (by simp [siPcs])
    exact nodeW_si_post hI bA1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case arg =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bArg rfl rArg_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr rArg_noRet) (fun _ _ _ => rfl) hsub hSM
  case rmw =>
    dsimp only [ReserveW]; rw [hI.labOk]
    refine nodeW_ldop_post hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk hph.rmwTk
      (fun σ _ hJ => hJ.2.2.2) hmN hunN hph.rmwIn (fun σ _ hJ => ?_) hsub
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.rmwUpd
  case bnd =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bBnd rfl rBnd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr rBnd_noRet) (fun _ _ _ => rfl) hsub hSM
  case j =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bJ rfl rJ_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j
      (hnr rJ_noRet) (fun _ _ _ => rfl) hsub hSM
  case ok =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bOk (ofNat4_zero _) rRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok
      (hret_of_run rRet_ok fun _ _ hJ => by
        dsimp only [rvN] at hJ ⊢
        rw [(rRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

/-- info: 'Spike.Lib.A64.Rt.Reserve.reserveW_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reserveW_post

end Reserve

end Spike.Lib.A64.Rt

