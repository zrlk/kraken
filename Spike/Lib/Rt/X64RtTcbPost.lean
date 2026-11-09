/-
**`scc_rt_alloc_tcb` inside `W` after the take, at a header `h`** (x86-64;
twin of `Spike/Lib/Rt/A64RtTcbPost.lean`): the node obligations `TcbWG`
(`Spike/Lib/Rt/X64RtTcbGN.lean`) of an `scc_rt_alloc_tcb` called once the
caller's stack range `rS` is taken (its nodes in the take's phase, the
frame condition carrying `StackM rS`), as
`Spike/Lib/Rt/X64RtReservePost.lean` for the reserve.

Per-call phase projection; generic multi-spawn wants a reserve/post-take
phase bit (trusted, cleanup list).

- `nodeW_fi_post`: an instruction with undefined flags after the take (the
  x86-64 length computation's `shr`/`and`/`imul`/`shl`/`or`; no A64 twin).
- `TcbPhGP`: `TcbPhG` without `noTk`, the take's phase kept across the
  counter's add (`rmwTk`); `TcbPhGP.of_tcbPhG` from `TcbPhG` at the empty
  take's phase.
- `tcbW_postG`: the node obligations from them, as `tcbW_genG`.

Deviations from the A64 twin: x86-64's nodes (one per block or single
instruction, `Spike/Lib/Rt/X64RtTcbGN.lean`), the 5-byte `lock xadd`, no
region alignment (`hal`), the frame `-184 .. 8`.
-/
import Spike.Lib.Rt.X64RtTcbG
import Spike.Lib.Rt.X64RtReservePost

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TN pnA pinA hdrBlk_eq rmwBlk_eq StackM)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (after)

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at an instruction with undefined flags** (`FI`) after the
take, as `nodeW_fi_pre`, the range in private memory (`hsub`). -/
theorem nodeW_fi_post {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {fi : FI}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_fi (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

end Node

namespace Tcb

open Spike.Lib.X64.Flow.Ret0.AllocTcb

/-- **`scc_rt_alloc_tcb`'s phase facts at `h` after the take**: as
`TcbPhG`, without `noTk`, every state at the add in the take's phase iff
its successors are (`rmwTk`). -/
structure TcbPhGP (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab ra : Label → Int64) (h n0 : BitVec 64) : Prop where
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
  rmwTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 5 m) ↔ Tk s
  rmwIn : ∃ v, (⟨pnA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 5).toBitVec.toNat))
    ⟨pnA lab, 8⟩ (fun old => (old.setWidth 64 + lenOf h).setWidth 128) = true
  hdrNo : ∀ j w, (⟨pinA lab + n0 + mOf h <<< 3, 8⟩, w) ∉ ownOf j

/-- **`TcbPhGP` from `TcbPhG`** at the empty take's phase, given the add's
`rmwTk`. -/
theorem TcbPhGP.of_tcbPhG {okPc : Nat → Bool} {ph : Nat → Nat} {Tk : State → Prop}
    {ownOf : Nat → List (Loc × Val)} {lab ra : Label → Int64} {h n0 : BitVec 64}
    (H : TcbPhG okPc ph (fun _ => False) ownOf lab ra h n0)
    (hTk : ∀ s : State, pcOf s = (rmwPc lab).toBitVec.toNat → ∀ m, Tk (after s 5 m) ↔ Tk s) :
    TcbPhGP okPc ph Tk ownOf lab ra h n0 :=
  ⟨H.e, H.entry, H.j1, H.len, H.l1, H.l2, H.l3, H.l4, H.l5, H.l6, H.arg, H.bnd, H.j2, H.o1, H.o2, H.o3, H.o4,
    H.o5, H.ret, H.fullNe, H.step, H.rmwOk, hTk, H.rmwIn, H.rmwUpd, H.hdrNo⟩

end Tcb

set_option hygiene false in
/-- A block of `scc_rt_alloc_tcb` after the take, no `ret`, no dead target
reached: its code, cover, phase field and no-`ret` lemma. -/
local macro "tblkP " ok:term:max f:term:max nr:term:max : tactic =>
  `(tactic| (
    dsimp only [TcbWG]
    rw [hI.labOk]
    exact blkW_post hI (by assumption) (by first | rfl | exact ofNat_zero' _) $ok hR hlo hhi
      (hC _ fun _ _ hJ => hJ.1) $f (hnr $nr) (fun _ _ _ => rfl) hsub hSM))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc_tcb` without an event (`leaq`, or
one clobbering the flags) after the take, at `l + off`. -/
local macro "tstepP " lem:ident l:term:max off:term:max z:term:max : tactic =>
  `(tactic| (
    dsimp only [TcbWG]
    rw [hI.labOk]
    have hs := hstep (lab $l + Int64.ofNat $off, $z) (by simp [stepPcs])
    exact $lem (p := lab $l + Int64.ofNat $off) hI (by assumption) rfl
      (by first | rfl | exact (ofNat_zero' _).symm) (hC _ fun _ _ hJ => hJ.1) hs.1 hs.2 hsub))

open Tcb Spike.Lib.X64.Flow.Ret0.AllocTcb in
/-- **`scc_rt_alloc_tcb`'s states at `h` are inside `SFacts` after the
take**: as `tcbW_genG`, its frame condition also `StackM rS` (kept by the
region's writes, `hSM`), `rS` in the pool (`hsub`), its phase facts
`TcbPhGP`. -/
theorem tcbW_postG {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : allocTcbIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi) (q : TcbGG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hph : TcbPhGP okPc ph Tk ownOf lab ra q.h q.n0)
    (hmP : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pnA lab, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨hdrA lab q, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (pnA lab) 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (hdrA lab q) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    ∀ i, TcbWG (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) q i := by
  have h := hin
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at h
  repeat (obtain ⟨h, _⟩ := h)
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hstep : ∀ pz ∈ stepPcs lab, okPc pz.1.toBitVec.toNat = true ∧
      ph (pz.1 + Int64.ofNat pz.2).toBitVec.toNat = ph pz.1.toBitVec.toNat := hph.step
  have hnr : ∀ {blk : List (Directive × Nat)}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
    fun hb _ _ _ _ _ k hk hr => (noRet_false hb k hk hr).elim
  intro i
  cases i
  case e => tblkP atPro_ok hph.e atPro_noRet
  case entry =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_post hI (by assumption) (ofNat_zero' _) atChk_ok hR hlo hhi (hC _ fun _ _ hJ => hJ.1) hph.entry
      (hnr atChk_noRet)
      (fun _ _ hJ => by
        dsimp only [tcbNG] at hJ ⊢
        rw [(atChk_walkG lab _ hJ.2).1]
        simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
        exact hph.fullNe)
      hsub hSM
  case j1 => tblkP atJ1_ok hph.j1 atJ1_noRet
  case len => tblkP atL0_ok hph.len atL0_noRet
  case shr1 => tstepP nodeW_fi_post lenL 11 3
  case l1 => tblkP atL1_ok hph.l1 atL1_noRet
  case and1 => tstepP nodeW_fi_post lenL 29 3
  case l2 => tblkP atL2_ok hph.l2 atL2_noRet
  case shr2 => tstepP nodeW_fi_post lenL 47 3
  case l3 => tblkP atL3_ok hph.l3 atL3_noRet
  case and2 => tstepP nodeW_fi_post lenL 65 3
  case l4 => tblkP atL4_ok hph.l4 atL4_noRet
  case imul1 => tstepP nodeW_fi_post lenL 95 4
  case l5 => tblkP atL5_ok hph.l5 atL5_noRet
  case shl1 => tstepP nodeW_fi_post lenL 132 3
  case l6 => tblkP atL6_ok hph.l6 atL6_noRet
  case lea1 => tstepP nodeW_si_post lenL 139 7
  case arg => tblkP atArg_ok hph.arg atArg_noRet
  case rmw =>
    dsimp only [TcbWG]; rw [hI.labOk]
    refine nodeW_xadd_post (p := rmwPc lab) hI hown (by assumption) (by rfl) rfl (hC _ fun _ _ hJ => hJ.1)
      hph.rmwOk hph.rmwTk (fun σ _ hJ => ?_) hmP hunP hph.rmwIn (fun σ _ hJ => ?_) hsub
    · obtain ⟨-, -, -, hc⟩ := hJ
      rw [← hc]
      simp [bAddr, Reg64s.get64]
    · obtain ⟨-, -, ha, -⟩ := hJ
      have he : σ.regs.get64 .rax = lenOf q.h := by rw [← ha]; rfl
      rw [he]
      exact hph.rmwUpd
  case bnd => tblkP atBnd_ok hph.bnd atBnd_noRet
  case j2 => tblkP atJ2_ok hph.j2 atJ2_noRet
  case ok => tstepP nodeW_si_post okL 0 7
  case o1 => tblkP atO1_ok hph.o1 atO1_noRet
  case imul2 => tstepP nodeW_fi_post okL 34 4
  case o2 => tblkP atO2_ok hph.o2 atO2_noRet
  case shl2 => tstepP nodeW_fi_post okL 53 3
  case o3 => tblkP atO3_ok hph.o3 atO3_noRet
  case shl3 => tstepP nodeW_fi_post okL 74 3
  case o4 => tblkP atO4_ok hph.o4 atO4_noRet
  case or1 => tstepP nodeW_fi_post okL 95 3
  case o5 => tblkP atO5_ok hph.o5 atO5_noRet
  case hdr =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have hs := hstep (lab okL + Int64.ofNat 140, 3) (by simp [stepPcs])
    refine nodeW_st_post (p := lab okL + Int64.ofNat 140) hI hown (by assumption) rfl rfl
      (hC _ fun _ _ hJ => hJ.1) hs.1 hs.2 (fun σ _ hJ => ?_) hmH hunH hph.hdrNo hsub
    obtain ⟨-, -, -, hc⟩ := hJ
    have he : σ.regs.rcx.toBitVec = hdrA lab q := hc
    simp [bAddr, Reg64s.get64, he]
  case ret =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_postA hI (by assumption) rfl atRet_ok hR hlo hhi (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbNG] at hJ ⊢
        rw [(atRet_walkG lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.nodeW_fi_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.nodeW_fi_post

/-- info: 'Spike.Lib.X64.Rt.Tcb.TcbPhGP.of_tcbPhG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Tcb.TcbPhGP.of_tcbPhG

/-- info: 'Spike.Lib.X64.Rt.tcbW_postG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.tcbW_postG
