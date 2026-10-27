/-
**The runtime's blocks and nodes inside `SFacts` with the placement given
per state** (option (b)): `CFacts` (`Spike/Lib/A64SegInst.lean`) asks the
source control placed at *every* state (`CFacts.place : ∀ s, Placed …`),
which only a control of immediates meets. Its consumers use the placement
at the instruction's own pre-state only, so these variants take the
control's shape facts (`CFactsC`) and the placement as a state obligation:
a `BlkW`/`NodeW`/`ExitW` of `Placed` with no outside move.

- `CFactsC`: `CFacts` without the placement; `CFacts.toC`, `CFacts.ofC`;
- `sfacts_doneR`, `sfacts_svcR`: `sfacts_done`, `sfacts_svc` at a placement
  at the state;
- `blkW_sfactsR`: `blkW_sfacts` with the placement a `BlkW` of `Placed`;
- `blkW_postOR`, `nodeW_svc_postOR`: `blkW_postO`, `nodeW_svc_postO`
  (`Spike/Lib/Rt/A64RtW.lean`) so;
- `mainSW_sfactsR`: `mainSW_sfacts` (`Spike/Lib/Rt/A64RtMainS.lean`) with
  the controls after the setup block and at the return point given by their
  shape facts, the placement a `BlkW` of the marshalling block (`hPlS`) and
  an `ExitW` of the tail (`hPlX`);
- `MainSW.ofPl`: `MainSW` of a state predicate from the entry's control's
  at every state, the marshalling block's and the tail's.
-/
import Spike.Lib.Rt.A64RtMainS

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1

/-- **`CFacts` without the placement**: the source control's shape facts
(no return, one-cell accesses, no allocation). -/
structure CFactsC (c : Ctl) : Prop where
  noRet : ∀ a, c.term ≠ .ret a
  cell : ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noAlloc : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e

/-- `CFacts` gives its shape facts. -/
theorem CFacts.toC {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} (h : CFacts Λ lbl c) : CFactsC c :=
  ⟨h.noRet, h.cell, h.noAlloc⟩

/-- `CFacts` from its shape facts and the placement at every state. -/
theorem CFacts.ofC {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} (h : CFactsC c) (hp : ∀ s, Placed Λ lbl s c) :
    CFacts Λ lbl c :=
  ⟨h.noRet, h.cell, h.noAlloc, hp⟩

section Ev

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {s : State} {c : Ctl}

open Kraken.Promising.Lower.A64 (CellAt after)

/-- **`SFacts` at an instruction without an event**, the control placed at
the state (`hpl`): `sfacts_done` at `CFactsC`. -/
theorem sfacts_doneR {s' : State} {d : Directive} {sz : Nat} (hC : CFactsC c) (hpl : Placed Λ lbl s c)
    (hP : PcOff μ s) (hc : CellAt s d sz) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hex : isaLSE2.exec s = some (.done s')) (hown : own s' = own s) (htk : Tk s' ↔ Tk s)
    (hO : Tk s → Owned Λ rS s) : SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = false := atSvc_false_of_cellAt hc hd
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun _ e he => ?_, hpl, fun h => ?_, hC.noAlloc,
    fun _ tree he => ?_, fun h => ?_, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ _ tree he => ?_,
    fun h => ?_, hO, abortOk_of_ne hP.noAbort, fun h => ?_⟩
  · rw [hex] at he; cases he; nofun
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact .inl ⟨hown, trivial⟩
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact htk
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

/-- **`SFacts` at `svc #0`**, the control placed at the state (`hpl`):
`sfacts_svc` at `CFactsC`. -/
theorem sfacts_svcR (hC : CFactsC c) (hpl : Placed Λ lbl s c) (hP : PcOff μ s)
    (hc : CellAt s Spike.Lib.A64.Flow.svcDir 4)
    (hnext : ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hnw : ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n)) :
    SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = true := atSvc_of_cellAt hc
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hc hd).1 hs'
    exact hnext _
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun h => ?_, hpl, fun _ => ⟨0, 4, hc⟩, hC.noAlloc,
    fun h => ?_, fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, abortOk_of_ne hP.noAbort, fun _ => hnw⟩
  all_goals (rw [hs] at h; cases h)

end Ev

section Blk

open Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)

/-- **A covered block's states carry `SFacts`, the placement per state**:
`blkW_sfacts` with the node's controls' shape facts (`hCC`) and the
control placed at every state of the block (`hPl`, a `BlkW` of `Placed`
with no outside move). -/
theorem blkW_sfactsR {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hCC : ∀ σ c, n.J σ c → CFactsC c)
    (hPl : BlkW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F n blk)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      PcOff μ s ∧ ∀ s', ¬ K s s')
    (hph : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s s' : State,
      s.exe = exe → s.endPc = endPc → s'.exe = exe → s'.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      own s' = own s ∧ (Tk s' ↔ Tk s))
    (hO : ∀ (s : State) m, F s.st.1 → DFrame R s.st.1 m → (∀ k, R.Off k → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ k < blk.length, ∀ s' : State, s'.st.1 = m → s'.st.2 = n.pc + Int64.ofNat (4 * k) → Tk s' → Owned Λ rS s') :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  intro s σ c he hn hdc hpc0 hA hF hJ k hk m hA' hD
  have hpl := (hPl s σ c he hn hdc hpc0 hA hF hJ k hk m hA' hD).1
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hl : labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [he]
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hal hlo hhi hc hreg hA'
  rw [hl] at hex
  obtain ⟨hown, htk⟩ := hph σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (4 * k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } he hn he hn rfl rfl
  exact sfacts_doneR (hCC σ c hJ) hpl hP hc (AI.not_svc hreg) hex hown htk
    (hO s m hF hD (fun k' hk' => Option.isSome_iff_exists.mpr (by
      obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩)) k hk _ rfl rfl)

end Blk

end Spike.Lib.A64Consumer

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackM StackOff stackOff_stable MainG limA tcbA_limA)
open Scc.Cert.Rt.A64 (blockAt OGrp OBlk Lays endOf label_labelGap)

section Blk

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- **A covered block after the take, the placement per state**:
`blkW_postO` with the node's controls' shape facts (`hCC`) and the
placement a `BlkW` of `Placed` (`hPl`). -/
theorem blkW_postOR {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64}
    {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hCC : ∀ σ c, n.J σ c → CFactsC c)
    (hPl : BlkW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F n blk)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [he] at hph
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfactsR hcode hok hR hal hlo hhi hCC hPl hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR (by omega) hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

end Blk

section Node

open Kraken.Promising.Lower.A64 (CellAt after)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at `svc #0` after the take, the placement per state**:
`nodeW_svc_postO` with the node's controls' shape facts (`hCC`) and the
placement a `NodeW` of `Placed` (`hPl`). -/
theorem nodeW_svc_postOR {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {k : Nat} {p : Int64} (hb : blockAt prog l k [svcDir] = true) (he : lab l + Int64.ofNat (4 * k) = p)
    (hp : n.pc = p) (hCC : ∀ σ c, n.J σ c → CFactsC c)
    (hPl : NodeW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F n)
    (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.X8.toNat ≠ 64) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn hdc hpc hA hD hJ hP hO =>
    sfacts_svcR (hCC σ c hJ) (hPl _s c ⟨hs, hn, hdc, hpc.trans hp.symm, σ, hA, hD, hJ⟩).1 hP
      (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.X8.toNat ≠ 64; rw [hA.regs]; exact hnr σ c hJ))

end Node

open MainS MainU

/-! ## `scc_rt_main` after a setup block -/

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- No `ret` in a block: `hret` of `blkW_postO(R)`, for any return address. -/
private theorem hnrR {blk : List Directive} (hb : noRetBlk blk = true) {n : ND} {ra' : Int64} :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
  fun _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states after a setup block are inside `SFacts`,
the placement per state** (`mainSW_sfacts`): the entry's control's
`CFacts` (`hC0`, placed at every state), the shape facts of the controls
back from the setup block (`hPostS`) and at the return point (`hPost`),
and their placement at the marshalling block's states (`hPlS`) and the
tail's (`hPlX`). -/
theorem mainSW_sfactsR {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {sc : SetupCode} (hin : mainSIn prog sc = true) {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {g : MainG} {x0 : BitVec 64} (hC0 : CFacts Λ lbl g.c0) (hPostS : ∀ c rs, PostS c rs → CFactsC c)
    (hPost : ∀ c v, Post c v → CFactsC c) (hph : MainPhS okPc ph lab sc)
    {R : Region} {F : MachineData → Prop}
    (hPlS : BlkW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F
      (mainS0 (_root_.Executable.labels exe).label sc PostS g x0) (marshal sc.sw sc.fn))
    (hPlX : ExitW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F
      (mainSR (_root_.Executable.labels exe).label sc Post) sc.k)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -sc.Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    MainSW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms sc PostS Post g x0 := by
  have H := mainSW_sfacts (μ := μ) (own := own) (Tk := Tk) (rS := rS) (ms := ms) (PostS := fun _ _ => False)
    (Post := fun _ _ => False) (x0 := x0) hI hin hC0 (fun _ _ h => h.elim) (fun _ _ h => h.elim) hph hR hal hlo
    hhi hl hh h16 hZ hsw hZw hk hmr hun hsub hfit hFO
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bMsh⟩, -⟩, bEx, bSvc⟩ := h
  have hR8 : R.base.toNat % 8 = 0 := by omega
  refine ⟨H.pro, H.call0, ?_, ?_⟩
  · rw [hI.labOk] at hPlS ⊢
    exact blkW_postOR hI bMsh (ofNat4_zero _)
      (okBlk_marshal (lo := -sc.Z.toInt) (hi := 0) (by omega) hsw _
        (fun i hi => by simp [Spike.Lib.offOk]; omega) (by simp [Spike.Lib.offOk]; omega))
      hR hal hlo hhi (fun _ _ hJ => hPostS _ _ hJ.1) hPlS hph.sp0 (hnrR (marshal_noRet _ _)) (fun _ _ _ => rfl)
      hl hh hsub hfit hFO
  · rw [hI.labOk] at hPlX ⊢
    refine ⟨?_, ?_⟩
    · exact blkW_postOR hI bEx (ofNat4_zero _) (exitTail_ok (lo := -sc.Z.toInt) (hi := 0) hk
          (by show (-sc.Z.toInt) % 16 = 0; omega)) hR hal hlo hhi (fun _ _ hJ => hPost _ _ hJ) hPlX.w0
        hph.ex (hnrR (exitTail_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    · exact nodeW_svc_postOR hI bSvc rfl (pc3 _).symm (fun _ _ ⟨_, _, hP, _⟩ => hPost _ _ hP) hPlX.w1
        hph.svc.1 hph.svc.2 hR hR8 hl hh hsub hFO (fun _ _ h => by rw [h.1]; decide)

end Main

/-! ## A state predicate over `scc_rt_main`'s own states -/

section Pl

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main`'s own states after a setup block meet a state
predicate** `P`, with no outside moves: the entry's control's at every
state (`h0`; the prologue and the setup call run at it), the marshalling
block's states' (`hS`) and the tail's (`hX`). -/
theorem MainSW.ofPl {P : Frag isaLSE2} {ms : MemSide isaLSE2} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
    {Post : Ctl → BitVec 64 → Prop} {g : MainG} {x0 : BitVec 64} (h0 : ∀ s, P s g.c0)
    (hS : BlkW P (fun _ _ => False) exe endPc R F
      (mainS0 (_root_.Executable.labels exe).label sc PostS g x0) (marshal sc.sw sc.fn))
    (hX : ExitW P (fun _ _ => False) exe endPc R F (mainSR (_root_.Executable.labels exe).label sc Post) sc.k) :
    MainSW P (fun _ _ => False) exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨fun _ _ _ _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨hJ.1.1 ▸ h0 _, fun _ h => h⟩,
      fun _ _ ⟨_, _, _, _, _, _, _, ⟨_, hJ, _⟩⟩ => ⟨hJ.1.1 ▸ h0 _, fun _ h => h⟩,
      fun _ _ _ _ _ _ _ _ _ ⟨_, _, hJ, _⟩ _ _ _ _ _ => ⟨hJ.1.1 ▸ h0 _, fun _ h => h⟩,
      fun _ _ _ _ _ _ _ _ _ ⟨_, _, hJ, _⟩ _ _ _ _ _ => ⟨hJ.1.1 ▸ h0 _, fun _ h => h⟩⟩,
    fun _ _ _ _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨hJ.1 ▸ h0 _, fun _ h => h⟩, hS, hX⟩

end Pl

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainSW_sfactsR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_sfactsR

/-- info: 'Spike.Lib.A64.Rt.MainSW.ofPl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MainSW.ofPl

end Spike.Lib.A64.Rt
