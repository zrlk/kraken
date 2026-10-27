/-
**`SFacts` at a control placed state by state** (x86-64; the twin of
`Spike/Lib/Rt/A64RtWR.lean`): `CFacts`' `place` asks the control placed in
every state, which a control back from a call holding a run-dependent
result in registers is not; these forms ask the control's other facts
(`CFactsC`) and its placement at each state the node or block reaches, as a
state obligation (`BlkW`/`NodeW`/`XExitW` of `Placed` with no outside move).

- `CFactsC`: `CFacts` without `place`; `CFacts.toC`, `CFacts.ofC`;
- `sfacts_doneR`, `sfacts_syscallR`: `sfacts_done`, `sfacts_syscall` at
  `CFactsC` and the placement at the state;
- `blkW_sfactsR`, `blkW_postOR`, `nodeW_syscall_postOR`: `blkW_sfacts`,
  `blkW_postO`, `nodeW_syscall_postO` at `CFactsC` of the node's controls
  (`hCC`) and the placement at its states (`hPl`);
- `BlkW.ofSt`: a block's states inside `P` when `P` holds at every state at
  the node's controls;
- `MainSW.ofPl`: `scc_rt_main`'s own states inside `P`, from `P` at every
  state at the entry's control and the state obligations of the marshalling
  block and the exit tail.
-/
import Spike.Lib.Rt.X64RtW
import Spike.Lib.Rt.X64MainS

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (StackOff stackOff_stable MainG)
open Scc.Cert.Rt.X64 (blockAtB)

/-! ## The control's facts without its placement -/

/-- **`CFacts` without `place`**: the source control's facts `SFacts` asks
of it alone, its placement left to each state. -/
structure CFactsC (c : Ctl) : Prop where
  noRet : ∀ a, c.term ≠ .ret a
  cell : ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noAlloc : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e

/-- `CFacts` has `CFactsC`. -/
theorem CFacts.toC {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} (h : CFacts Λ lbl c) : CFactsC c :=
  ⟨h.noRet, h.cell, h.noAlloc⟩

/-- `CFactsC` and the placement at every state are `CFacts`. -/
theorem CFacts.ofC {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} (h : CFactsC c) (hp : ∀ s, Placed Λ lbl s c) :
    CFacts Λ lbl c :=
  ⟨h.noRet, h.cell, h.noAlloc, hp⟩

/-! ## At one instruction -/

section Ev

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {s : State} {c : Ctl}

open Kraken.Promising.Lower.X64 (CellAt after op64)

/-- **`SFacts` at an instruction without an event**, the control's facts
`CFactsC` and its placement at `s` (`sfacts_done`). -/
theorem sfacts_doneR {s' : State} {d : Directive} {sz : Nat} (hC : CFactsC c) (hpl : Placed Λ lbl s c)
    (hP : PcOff μ s) (hc : CellAt s d sz) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall))
    (hex : isa.exec s = some (.done s')) (hown : own s' = own s) (htk : Tk s' ↔ Tk s)
    (hO : Tk s → Owned Λ rS s) : SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = false := atSyscall_false_of_cellAt hc hd
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun _ e he => ?_, hpl, fun h => ?_, hC.noAlloc,
    fun _ tree he => ?_, fun h => ?_, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun _ _ tree he => ?_, fun h => ?_, hO, abortOk_of_ne hP.noAbort, fun h => ?_⟩
  · rw [hex] at he; cases he; nofun
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact .inl ⟨hown, trivial⟩
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact htk
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

/-- **`SFacts` at a `syscall`**, the control's facts `CFactsC` and its
placement at `s` (`sfacts_syscall`). -/
theorem sfacts_syscallR {z : Nat} (hC : CFactsC c) (hpl : Placed Λ lbl s c) (hP : PcOff μ s)
    (hc : CellAt s (op64 .syscall) z)
    (hnext : ∀ m, own (after s z m) = own s ∧ (Tk (after s z m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hnw : ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n)) :
    SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = true := atSyscall_of_cellAt hc
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call _ s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | head => exact hnext _
      | tail _ h => cases h
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      exact hnext _
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun h => ?_, hpl, fun _ => ⟨z, hc⟩, hC.noAlloc,
    fun h => ?_, fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, abortOk_of_ne hP.noAbort, fun _ => hnw⟩
  all_goals (rw [hs] at h; cases h)

end Ev

/-! ## At a block or a node -/

section Blk

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

open Kraken.Promising.Lower.X64 (labelAddr)

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block's states carry `SFacts`** (`blkW_sfacts`), the
node's controls' `CFactsC` (`hCC`) and their placement at the block's
states (`hPl`) in place of `CFacts`. -/
theorem blkW_sfactsR {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hCC : ∀ σ c, n.J σ c → CFactsC c)
    (hPl : BlkW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F n blk)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk k) → PcOff μ s ∧ ∀ s', ¬ K s s')
    (hph : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s s' : State,
      s.exe = exe → s.endPc = endPc → s'.exe = exe → s'.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk k) →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      own s' = own s ∧ (Tk s' ↔ Tk s))
    (hO : ∀ (s : State) m, F s.st.1 → DFrame R s.st.1 m → (∀ k, R.Off k → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ k < blk.length, ∀ s' : State, s'.st.1 = m → s'.st.2 = n.pc + Int64.ofNat (cellOff blk k) → Tk s' →
        Owned Λ rS s') :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  intro s σ c he hn hdc hpc0 hA hF hJ k hk m hA' hD
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } he hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : Kraken.Promising.Lower.X64.CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
      a.toDir blk[k].2 :=
    (hcode s he hn).cell hd rfl rfl rfl
  have hl : labelAddr { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } =
      (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hlo hhi hc hreg hA'
  rw [hl] at hex
  obtain ⟨hown, htk⟩ := hph σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } he hn he hn rfl rfl
  exact sfacts_doneR (hCC σ c hJ) (hPl s σ c he hn hdc hpc0 hA hF hJ k hk m hA' hD).1 hP hc
    (AI.not_syscall hreg) hex hown htk
    (hO s m hF hD (fun k' hk' => Option.isSome_iff_exists.mpr (by
      obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩)) k hk _ rfl rfl)

/-- **A covered block after the switch** (`blkW_postO`), the node's
controls' `CFactsC` (`hCC`) and their placement at the block's states
(`hPl`) in place of `CFacts`. -/
theorem blkW_postOR {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hCC : ∀ σ c, n.J σ c → CFactsC c)
    (hPl : BlkW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F n blk)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfactsR hcode hok hR hlo hhi hCC hPl hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

/-- **A node at a `syscall`** after the switch (`nodeW_syscall_postO`), the
node's controls' `CFactsC` (`hCC`) and their placement at its states
(`hPl`) in place of `CFacts`. -/
theorem nodeW_syscall_postOR {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {R : Region} {F : MachineData → Prop} {n : ND}
    {z : Nat} {l : Label}
    {off : Nat} {p : Int64} (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hCC : ∀ σ c, n.J σ c → CFactsC c)
    (hPl : NodeW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F n)
    (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn hdc hpc hA hD hJ hP hO =>
    sfacts_syscallR (hCC σ c hJ) (hPl _s c ⟨hs, hn, hdc, hpc.trans hp.symm, σ, hA, hD, hJ⟩).1 hP
      (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

end Blk

/-! ## `scc_rt_main`'s own states from state obligations -/

section MainPl

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {P : Frag isa}

/-- **A block's states inside `P`**, with no outside move, from `P` at
every state at each of the node's controls. -/
theorem BlkW.ofSt {n : ND} {blk : List (Directive × Nat)} (h : ∀ σ c, n.J σ c → ∀ s, P s c) :
    BlkW P (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ _, fun _ h => h⟩

/-- **A node's states inside `P`**, with no outside move, from `P` at every
state at each of the node's controls. -/
theorem NodeW.ofSt {n : ND} (h : ∀ σ c, n.J σ c → ∀ s, P s c) : NodeW P (fun _ _ => False) exe endPc R F n :=
  fun _ c hA => ⟨h _ c hA.2.2.2.2.choose_spec.2.2 _, fun _ h => h⟩

/-- **`scc_rt_main`'s own states inside `P`**, with no outside move: the
prologue's and the setup call block's from `P` at every state at the
entry's control (`h0`), the marshalling block's (`hS`) and the exit tail's
(`hX`) as given. -/
theorem MainSW.ofPl {ms : MemSide isa} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
    {Post : Ctl → BitVec 64 → Prop} {g : MainG} {x0 : BitVec 64} (h0 : ∀ s, P s g.c0)
    (hS : BlkW P (fun _ _ => False) exe endPc R F (mainS0R (_root_.Executable.labels exe).label sc PostS g x0)
      (marshal sc.sw sc.fn))
    (hX : Spike.Lib.X64.Flow.XExitW P (fun _ _ => False) exe endPc R F
      (mainSRR (_root_.Executable.labels exe).label sc Post) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5) :
    MainSW P (fun _ _ => False) exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨BlkW.ofSt fun _ _ hJ => hJ.1.1 ▸ h0, BlkW.ofSt fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ h0,
      NodeW.ofSt fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ h0, BlkW.ofSt fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ h0,
      BlkW.ofSt fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ h0⟩,
    BlkW.ofSt fun _ _ hJ => hJ.1.1 ▸ h0, hS, hX⟩

end MainPl

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.blkW_postOR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_postOR

/-- info: 'Spike.Lib.X64.Rt.nodeW_syscall_postOR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_syscall_postOR

/-- info: 'Spike.Lib.X64.Rt.MainSW.ofPl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MainSW.ofPl

end Spike.Lib.X64.Rt
