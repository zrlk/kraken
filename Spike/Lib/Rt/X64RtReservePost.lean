/-
**`scc_rt_thread_reserve` inside `W` after the take** (x86-64; twin of
`Spike/Lib/Rt/A64RtReservePost.lean`): the node obligations `ReserveW`
(`Spike/Lib/Rt/X64RtReserve.lean`) of a reserve called once the caller's
stack range `rS` is taken, so its nodes are in the take's phase and the
frame condition carries `StackM rS`.

- `nodeW_xadd_post`: an owned word's `lock xaddq %r, k(%b)` after the take,
  the take's phase kept across it by a premise on its pc (`hTk`) rather
  than by the phase index (the counter's add may switch phase bits the
  take's phase ignores). A64's `nodeW_ldop_post`.
- `ResPhP`: `ResPh` without `noTk`, with the take's phase kept across the
  add (`rmwTk`); `ResPhP.of_resPh` from `ResPh` at the empty phase.
- `rmwTk_of_ph`: `rmwTk` through the phase index.
- `reserveW_post`: the node obligations from them, as `reserveW_gen`.

Deviations from the A64 twin: the add is the 5-byte `lock xadd` at
`rmwPc = entry + 22` (A64's 4-byte `ldadd`), x86-64 has no `add` node and
the region needs no alignment (`hal`); its frame is `-40 .. 8`.
-/
import Spike.Lib.Rt.X64RtReserve

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt after exec_xaddG_agrees eaddr)

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at an owned word's `lock xaddq %r, k(%b)`** after the take,
as `nodeW_xadd_pre`: the word `a` (`ha`), owned at `p` (`hin`), updated at
the next pc (`hupd`); every state at `p` in the take's phase iff its
successors are (`hTk`), the range in private memory (`hsub`). -/
theorem nodeW_xadd_post {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} {a : BitVec 64} (hb : blockAtB cells l off [(xaddDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hTk : ∀ s : State, pcOf s = p.toBitVec.toNat → ∀ m, Tk (after s z m) ↔ Tk s)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (old.setWidth 64 + σ.regs.get64 r).setWidth 128) = true)
    (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_xaddG_agrees (w := .W64) hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    have hpc4 : ∀ m, (after s z m).st.2 = p + Int64.ofNat z := fun _ => by rw [← hpc]
    obtain ⟨hT'', hown', htk⟩ := rmw_facts (Λ := Λ) (own := own) (Tk := Tk) (s := s) (k := .acqRel)
      (nr := false) (z := z)
      (op := fun old => some ((old.setWidth 64 + s.st.1.regs.get (.low r .W64)).setWidth 128))
      (m := fun v => { s.st.1 with
        regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64)
        status := LockBinOp.add.status (v.setWidth 64) (s.st.1.regs.get (.low r .W64))
          (v.setWidth 64 + s.st.1.regs.get (.low r .W64)) false })
      hmw (fun _ => hTk s (by unfold pcOf; rw [hpc]) _) (by rw [own_at hown hpc]; exact hin)
      (fun v hv => by
        rw [own_at hown hpc, own_at hown (hpc4 _), Option.getD_some, Reg64s.get_low64, hA.regs]
        rw [own_at hown hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown' htk hO

end Node

namespace Reserve

open Kraken.X64.Parser
open Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Reserve
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)

/-- **`scc_rt_thread_reserve`'s phase facts after the take**: as `ResPh`,
without `noTk` (its nodes are in the take's phase), every state at the add
in the take's phase iff its successors are (`rmwTk`). -/
structure ResPhP (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab : Label → Int64) (ra : Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat 0) ra rPro = true
  arg : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 7) ra rArg = true
  bnd : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 27) ra rBnd = true
  j : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 65) ra rJ = true
  ok : blkPh okPc ph (fun _ => false) lab (lab okL + Int64.ofNat 0) ra rRet = true
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 7).toBitVec.toNat = ph p.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  rmwTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 5 m) ↔ Tk s
  rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 5).toBitVec.toNat))
    ⟨ntA lab, 8⟩ (fun old => (old.setWidth 64 + 1#64).setWidth 128) = true

/-- **The add's `rmwTk` from a take's phase through the phase index**:
`Tk` a predicate `TkW` of the phase, which agrees at the add and past it. -/
theorem rmwTk_of_ph {ph : Nat → Nat} {TkW : Nat → Prop} {lab : Label → Int64}
    (h : TkW (ph (rmwPc lab + Int64.ofNat 5).toBitVec.toNat) ↔ TkW (ph (rmwPc lab).toBitVec.toNat)) :
    ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m,
      TkW (ph (pcOf (after s 5 m))) ↔ TkW (ph (pcOf s)) := by
  intro s hs m
  have he : s.st.2 = rmwPc lab := by
    unfold pcOf at hs
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq hs)
  have h5 : pcOf (after s 5 m) = (rmwPc lab + Int64.ofNat 5).toBitVec.toNat := by
    show (s.st.2 + Int64.ofNat 5).toBitVec.toNat = _; rw [he]
  rw [h5, hs]; exact h

/-- **`ResPhP` from `ResPh`** at the empty take's phase (whose `noTk` is
trivial), given the add's `rmwTk`. -/
theorem ResPhP.of_resPh {okPc : Nat → Bool} {ph : Nat → Nat} {Tk : State → Prop}
    {ownOf : Nat → List (Loc × Val)} {lab : Label → Int64} {ra : Int64}
    (h : ResPh okPc ph (fun _ => False) ownOf lab ra)
    (hTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 5 m) ↔ Tk s) :
    ResPhP okPc ph Tk ownOf lab ra :=
  ⟨h.e, h.arg, h.bnd, h.j, h.ok, h.si, h.rmwOk, hTk, h.rmwIn, h.rmwUpd⟩

/-- **`scc_rt_thread_reserve`'s states are inside `SFacts` after the
take**: as `reserveW_gen`, its frame condition also `StackM rS` (kept by
the region's writes, `hSM`), `rS` in the pool (`hsub`), its phase facts
`ResPhP`. -/
theorem reserveW_post {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : reserveIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi) (q : ResG)
    (hq : q.c0 = c0) (hra : q.g.ra = ra.toBitVec) (hph : ResPhP okPc ph Tk ownOf lab ra)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨ntA lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA lab) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    ∀ i, ReserveW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) q i := by
  have h := hin
  simp only [reserveIn, siAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hnr : ∀ {blk : List (Directive × Nat)}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
    fun hb _ _ _ _ _ k hk hr => (noRet_false hb k hk hr).elim
  intro i
  cases i
  case e =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bE (ofNat_zero' _) rPro_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr rPro_noRet) (fun _ _ _ => rfl) hsub hSM
  case entry =>
    dsimp only [ReserveW]; rw [hI.labOk]
    have := hph.si (lab entryL + Int64.ofNat 0) (by simp [siPcs])
    exact nodeW_si_post hI bA rfl (ofNat_zero' _).symm (hC _ fun _ _ hJ => hJ.1) this.1 this.2 hsub
  case arg =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bArg rfl rArg_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr rArg_noRet) (fun _ _ _ => rfl) hsub hSM
  case rmw =>
    dsimp only [ReserveW]; rw [hI.labOk]
    refine nodeW_xadd_post (p := rmwPc lab) hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk
      hph.rmwTk (fun σ _ hJ => ?_) hmN hunN hph.rmwIn (fun σ _ hJ => ?_) hsub
    · obtain ⟨-, -, -, hc⟩ := hJ
      rw [← hc]
      simp [bAddr, Reg64s.get64]
    · obtain ⟨-, -, ha, -⟩ := hJ
      have he : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
      rw [he]
      exact hph.rmwUpd
  case bnd =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bBnd rfl rBnd_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr rBnd_noRet) (fun _ _ _ => rfl) hsub hSM
  case j =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_post hI bJ rfl rJ_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j
      (hnr rJ_noRet) (fun _ _ _ => rfl) hsub hSM
  case ok =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_postA hI bOk (ofNat_zero' _) rRet_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok
      (hret_of_run rRet_ok fun _ _ hJ => by
        dsimp only [rvN] at hJ ⊢
        rw [(rRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Reserve

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.nodeW_xadd_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.nodeW_xadd_post

/-- info: 'Spike.Lib.X64.Rt.Reserve.rmwTk_of_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.rmwTk_of_ph

/-- info: 'Spike.Lib.X64.Rt.Reserve.ResPhP.of_resPh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.ResPhP.of_resPh

/-- info: 'Spike.Lib.X64.Rt.Reserve.reserveW_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.reserveW_post
