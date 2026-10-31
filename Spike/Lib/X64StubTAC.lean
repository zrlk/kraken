/-
**The threads abort path's obligations inside `SFactsAC`** (x86-64): the
`Abort.Disp.StubTW` of a call to `scc_rt_abort` with `%rdi = 5` and the
return address `raT lab pfx` (`Spike/Lib/X64AbortThreadsW.lean`) at
`W := SFactsAC … frs Dt (fun _ => False) Cl (ThreadsAb.Ac lab pfx)`, the
twin of `Spike/Lib/X64StubWA.lean` (the write path inside `SFactsA`), for any
program with the abort code (`Scc.Cert.Rt.X64.Abort.abortIn`), an instance's
facts at the frames `frs` and the path's phase check (`abortPhThreadsOk`,
`Spike/Lib/X64AbortPhT.lean`). The x86-64 twin of
`Spike/Lib/A64StubTAC.lean` (same names).

The write abort phase is empty (`Ab := fun _ => False`, no `write` refusal
after a spawn); every state of the path is in the threads abort phase `Ac`
(`Spike/Lib/X64ThreadsAb.lean`), so its `AcSt` is `AcSt.of_ac`.

* `sfactsAC_doneT`, `sfactsAC_svcT`: `SFactsAC` in the phase `Ac` at an
  instruction without an event off the sites, and at a `syscall` with the
  threads abort facts and the write tail given;
* `ac_g5A`, `ac_stubA`: the jump to the stub's and the stub's states in `Ac`
  from the abstract state;
* `blkW_threadsAC`, `nodeW_si_threadsAC`: a block and a single instruction of
  the path, each state in the phase (`hAc`);
* `seg_svcTW`, `stubTW_of_code`: the stub's `write` call over `NT` and
  `StubTW` from the abort code (`stubWW_of_code`'s twin);
* `stubTW_sfactsAC`: `StubTW` inside `SFactsAC`, the exit call the threads
  abort site.

**Unlike AArch64**: the return address is the pushed word at the frame's
`slot 8`, not `x30`, so `ac_g5A`/`ac_stubA` take `R.Off 8`, the offsets'
position (`ThreadsAcSt.RaPos`) and `σ.slot 8 = raT` (`raW_of_abs`), and
`nodeW_si_threadsAC`'s `hAc` reads the node's invariant and abstract state
as the A64 one does; the system call is a `syscall` of `z` bytes (`ownSys`
also covers `arch_prctl`'s resumed state), so `sfactsAC_svcT` (A64 name
kept) is at `op64 .syscall` and `seg_svcTW` is over `NT … .sys` (the next pc
`+36 = +34+2`); instructions have sizes (a block's pcs are its label's plus
`cellOff`); the stub has no `n1b` node (its `leaq` is one instruction), so
`stubTW_of_code` has no `sn1b`; the region is `[-24, 16)` from the frame
base with `R.base` 8-aligned (`hR8`, no `hal`).

Concrete k=5 over `NT`; to be folded into the generic abort files together
with `Abort.NT` (pre-hello.w-release cleanup).
-/
import Spike.Lib.X64StubWA
import Spike.Lib.X64AbortPhT
import Spike.Lib.X64AbortThreadsW
import Spike.Lib.X64SFactsAC
import Spike.Lib.X64ThreadsAcSt

namespace Spike.Lib.X64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf abi atSyscall_of_cellAt atSyscall_false_of_cellAt mem_certSuccs_syscall
  certSuccs_archSetFs)
open Spike.Lib.Consumer1 (allInv_true OneCellTy)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerS (OwnS PlacedS)
open Spike.Lib.X64ConsumerA
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (StackOff stackOff_stable)
open Spike.Lib.X64.Rt (InstOk owned_off)
open Scc.Cert.Rt.X64 (blockAtB code_field Lays endOf)
open Kraken.Promising.Lower.X64 (op64)

/-! ## `SFactsAC` at one state in the phase -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt : State → Prop} {F : MachineData → Prop}
  {Cl Ac : State → Prop}

open Kraken.Promising.Lower.X64 (CellAt after)

/-- **`SFactsAC` in the phase `Ac` at an instruction without an event** (not
a `syscall`, its step `.done s'`), off the marks' sites, at a control with
`RefCtl`'s facts (`sfactsA_doneW` with no write abort phase): the leaf owns
what `s` owns and is in the take phase iff `s` is; `Cl` at `s` is at a
`clone` (`hClS`). -/
theorem sfactsAC_doneT {s' : State} {d : Directive} {sz : Nat} (hc : RefCtl Λ p own lbl F c fs)
    (hpl : Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs) (hP : PcOff μ s)
    (hcl : CellAt s d sz) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec s = some (.done s'))
    (hown : own s' fs = own s fs) (htk : Tk s' ↔ Tk s) (hO : Tk s → Owned Λ rS s) (hAc : Ac s)
    (hClS : Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) Cl Ac := by
  have hs : abi.atSys s = false := atSyscall_false_of_cellAt hcl hd
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hP.noSite
      mapped := fun _ e he => by rw [hex] at he; cases he; nofun
      place := hpl
      svc := fun h => by rw [hs] at h; cases h
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun c' fs' hr _ tree he => by
        rw [hex] at he; cases he
        refine .inl ⟨?_, trivial⟩
        show own s' fs' = own s fs'
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact hown
      ownSys := fun _ _ _ h => by rw [hs] at h; cases h
      ownTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      site := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkInstr := fun _ _ tree he => by rw [hex] at he; cases he; exact htk
      tkSys := fun h => by rw [hs] at h; cases h
      owned := hO
      wrTail := fun h => by rw [hs] at h; cases h
      wr := fun _ _ _ _ => wrOkA_of_noWr (noWr_done hex)
      zero := hc.zero
      abortOk := fun k a ha hpc => (hP.noAbort k a ha hpc).elim
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false
      acSt := AcSt.of_ac hAc
      clSvc := hClS }

/-- **`SFactsAC` in the phase `Ac` at a `syscall`** of `z` bytes off the
release and take sites, at a control with `RefCtl`'s facts, with the threads
abort facts (`hab`) and the write tail (`hwr`) given (`sfactsA_sysW` with no
write abort phase; the A64 name `svc` kept): every state the kernel resumes
in is past it, owning what `s` owns and in the take phase iff `s` is. -/
theorem sfactsAC_svcT {z : Nat} (hc : RefCtl Λ p own lbl F c fs)
    (hpl : Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hcl : CellAt s (op64 .syscall) z)
    (hnext : ∀ m, own (after s z m) fs = own s fs ∧ (Tk (after s z m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .threads ∧
      ∀ v, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) →
        v % 256 = Scc.Sem.Kernel.abortStatus)
    (hwr : ∀ fd buf n, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s)
    (hAc : Ac s)
    (hClS : Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) Cl Ac := by
  have hs : abi.atSys s = true := atSyscall_of_cellAt hcl
  have hsucc : ∀ call, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call, own s' fs = own s fs ∧ (Tk s' ↔ Tk s) := by
    intro call _ s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hcl a] at hs'
      cases hs' with
      | head => exact hnext _
      | tail _ h => cases h
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hcl fun a he => ha ⟨a, he⟩).1 hs'
      exact hnext _
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hrel
      mapped := fun h => by rw [hs] at h; cases h
      place := hpl
      svc := fun _ => ⟨z, hcl⟩
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun _ _ _ h => by rw [hs] at h; cases h
      ownSys := fun c' fs' hr _ call hd s' hs' => by
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact (hsucc call hd s' hs').1
      ownTake := fun a ha hpc => (htake a ha hpc).elim
      site := fun a ha hpc => (htake a ha hpc).elim
      tkTake := fun a ha hpc => (htake a ha hpc).elim
      tkInstr := fun _ h => by rw [hs] at h; cases h
      tkSys := fun _ call hd s' hs' => (hsucc call hd s' hs').2
      owned := hO
      wrTail := fun _ => hwr
      wr := fun _ _ _ h => by rw [hs] at h; cases h
      zero := hc.zero
      abortOk := fun k a ha hpc => let ⟨h1, h2⟩ := hab k a ha hpc; ⟨.inr (.inr (.inr ⟨h1, hAc⟩)), h2⟩
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false
      acSt := AcSt.of_ac hAc
      clSvc := hClS }

end State

/-! ## The stub's states in the phase -/

section Phase

variable {lab : Label → Int64} {pfx : String}

/-- A state of the jump to the threads stub with the threads return address
at `slot 8`, from the abstract state, is in `Ac`. -/
theorem ac_g5A {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS}
    (hmem : s.st.2 ∈ ThreadsAb.g5Pcs lab) (hA : Abs R o s.st.1 σ) (hoff : R.Off 8)
    (hpos : ThreadsAcSt.RaPos lab s.st.2 o) (hr : σ.slot 8 = ThreadsAb.raT lab pfx) :
    ThreadsAb.Ac lab pfx s :=
  ThreadsAb.ac_g5 hmem (ThreadsAcSt.raW_of_abs hA hoff hpos hr)

/-- A state of the threads stub with the threads return address at
`slot 8`, from the abstract state, is in `Ac`. -/
theorem ac_stubA {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS}
    (hmem : s.st.2 ∈ ThreadsAb.stubPcs lab) (hA : Abs R o s.st.1 σ) (hoff : R.Off 8)
    (hpos : ThreadsAcSt.RaPos lab s.st.2 o) (hr : σ.slot 8 = ThreadsAb.raT lab pfx) :
    ThreadsAb.Ac lab pfx s :=
  ThreadsAb.ac_stub hmem (ThreadsAcSt.raW_of_abs hA hoff hpos hr)

end Phase

/-! ## The path's blocks and single instructions -/

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop} {Cl Ac : State → Prop}

/-- **A block of the threads abort path inside `SFactsAC`** at the frames
`frs`: as `blkW_writeA` with no write abort phase, each state before an
instruction in the phase `Ac` (`hAc`), every `Cl` state at a `clone`
(`hCl`). -/
theorem blkW_threadsAC {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {off : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat off) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hAc : ∀ (s : State) σ c j m, n.J σ c → j < blk.length →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      Ac { s with st := (m, n.pc + Int64.ofNat (cellOff blk j)) }) :
    BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl Ac)
      K exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  rw [he, ← hI.labOk] at hph
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
  intro s σ c hs hn _ _ hA hD hJc k hk m hA' hDm
  have hac := hAc s σ c k m hJc hk hA'
  obtain rfl := hJ σ c hJc
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } hs hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hcell : Kraken.Promising.Lower.X64.CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
      a.toDir blk[k].2 :=
    (hcode s hs hn).cell hd rfl rfl rfl
  have hlA : Kraken.Promising.Lower.X64.labelAddr { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } =
      (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [hs]
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hlo hhi hcell hreg hA'
  rw [hlA] at hex
  obtain ⟨hown, htk⟩ := hph' σ c hJc k hk a hca { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } hs hn hs hn rfl rfl
  exact sfactsAC_doneT hc (hc.place _ (hF _ _ hD hDm)) hP hcell (AI.not_syscall hreg) hex
    hown htk (fun _ => owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hD) hDm)
      fun k' hk' => Option.isSome_iff_exists.mpr (by obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩))
    hac (hCl _)

/-- **A single instruction without an event (`SI`) of the threads abort path
inside `SFactsAC`**: as `nodeW_si_writeA` with no write abort phase, every
state at its pc in the phase `Ac` from the node's invariant and abstract
state (`hAc`), every `Cl` state at a `clone` (`hCl`). -/
theorem nodeW_si_threadsAC {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {si : SI} {l : Label} {off z : Nat} {q : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off [(si.toDir, z)] = true) (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (hok : okPc q.toBitVec.toNat = true) (hph : ph (q + Int64.ofNat z).toBitVec.toNat = ph q.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hAc : ∀ (s : State) σ c, n.J σ c → Abs R n.o s.st.1 σ → s.st.2 = q → Ac s) :
    NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl Ac)
      K exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJc⟩
  rw [hp] at hpc
  have hac := hAc s σ c hJc hA hpc
  obtain rfl := hJ σ c hJc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  have hcell := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hnx := Spike.Lib.X64.Rt.next_same hI hpc hph
  refine ⟨sfactsAC_doneT hc (hc.place s hD) hP.1 hcell
    (by cases si <;> intro w w' h <;> cases h) (exec_si hcell) (hnx _).1 (hnx _).2
    (fun _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => ?_) hac (hCl s), hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

end Nodes

/-! ## The stub's `write` call and `StubTW` from the code -/

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} {W : Frag isa} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A stub's `write` system call with the return address inside `W`**
(`seg_syscallW` over `Abort.NT`; the A64 name `svc` kept): a segment to its
next node, given its code and its states inside `W`. -/
theorem seg_svcTW {st : Abort.Stub} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (Abort.NT (_root_.Executable.labels exe).label st c0 ra .sys).pc [(op64 .syscall, 2)])
    (hW : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label st c0 ra .sys)) :
    SegW W K p lbl ms (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label st c0 ra .sys))
      (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label st c0 ra .n5)) := by
  refine (syscall_ndW (N := fun _ : Unit => Abort.NT (_root_.Executable.labels exe).label st c0 ra .n5)
    (E := fun e : Empty => e.elim) hK hF hcode hW ?_ ?_).mono_post ?_
  · rintro σ c ⟨hJ, h0, ha⟩
    obtain ⟨buf, n, hc⟩ := syscallCall_write ha h0
    refine ⟨_, hc, nofun, fun v _ => ⟨c, .refl c, .inl ⟨(), ?_,
      by simp [Abort.NT, Abort.oI, syscallSO, SO.le, SO.kill]; decide, hJ⟩⟩⟩
    show _ + 36 = _ + 34 + Int64.ofNat 2
    rw [Int64.add_assoc]; rfl
  · rintro s c σ call - ⟨-, h0, ha⟩ hcall
    obtain ⟨buf, n, hc⟩ := syscallCall_write ha h0
    rw [hc] at hcall
    cases hcall
    exact ⟨nofun, nofun, fun fd b n' h => by cases h; decide, fun _ h => by cases h⟩
  · rintro s c (⟨_, h⟩ | ⟨x, _⟩)
    · exact h
    · exact x.elim

/-- **The threads abort path's obligations from the abort code**: `StubTW`
for code cells with `abortIn` (`stubWW_of_code`'s twin), given the
dispatcher's nodes at code 5 and the threads stub's nodes with the return
address inside `W` (the stub's `write` call among them, `hsys`) and the exit
call at an abort site (`hab`). -/
theorem stubTW_of_code {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (de : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .e) Abort.Disp.d0)
    (dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t1) Abort.Disp.t1)
    (dj1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j1) Abort.Disp.j1)
    (dt2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t2) Abort.Disp.t2)
    (dj2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j2) Abort.Disp.j2)
    (dt3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t3) Abort.Disp.t3)
    (dj3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j3) Abort.Disp.j3)
    (dt4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t4) Abort.Disp.t4)
    (dj4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j4) Abort.Disp.j4)
    (dt5 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t5) Abort.Disp.t5)
    (dg5 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .g5) Abort.Disp.g5)
    (se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .e) Abort.x0)
    (sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n1))
    (sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n2)
      Abort.x1Threads)
    (hsys : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .sys))
    (sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n5) Abort.x2)
    (sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .ex))
    (hab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubTW W K p lbl ms exe endPc R F c0 ra := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hpr
  have hst := hpr.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, hsysIn, -⟩ := hst
  exact ⟨Scc.Cert.Rt.X64.Abort.code_disp hp hend hpr.2, de, dt1, dj1, dt2, dj2, dt3, dj3, dt4, dj4, dt5, dg5,
    Scc.Cert.Rt.X64.Abort.code_stubs hp hend hprog .threads, se, sn1, sn2, sn5, sex,
    seg_svcTW hK hF (code_field hp hend hsysIn rfl) hsys, hab⟩

end Code

/-! ## `StubTW` inside `SFactsAC` (the phase check `abortPhThreadsOk`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {R : Region} {F : MachineData → Prop}

open Spike.Lib.X64ConsumerA.ThreadsAcSt

set_option maxHeartbeats 800000 in
/-- **The threads abort path's obligations inside `SFactsAC … frs Dt
(fun _ => False) Cl (ThreadsAb.Ac lab pfx)`** (`Abort.Disp.StubTW` at the
return address `ThreadsAb.raT lab pfx`), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`); as `stubWW_sfactsA`. Every `Cl` state is at a `clone`
(`hCl`). The exit call is the threads abort site: off the release and take
sites (`hrel`, `htk`), no other kind's (`hk`), no outside move (`hKex`), the
memory side's abort (`hms`). The write tail `Dt` holds at the stub's
`write` (`hwr`). -/
theorem stubTW_sfactsAC {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop} {pfx : String} {Cl : State → Prop}
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhThreadsOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.threads.exit).toBitVec.toNat = a → k = .threads)
    (hKex : ∀ s s', pcOf s = (lab Abort.threads.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.threads.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.NT lab Abort.threads c0 (ThreadsAb.raT lab pfx) .sys) s c → Dt s) :
    Abort.Disp.StubTW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
        (ThreadsAb.Ac lab pfx))
      K p al ms exe endPc R F c0 (ThreadsAb.raT lab pfx) := by
  have hlab := hI.labOk
  subst hlab
  have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have hoff8 : R.Off 8 := ⟨by decide, by omega, by omega⟩
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hb1, hsysIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  simp only [abortPhThreadsOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pj4, pt5, pg5, pb0, o1, q1, pb1, o34, q34, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he34 : (_root_.Executable.labels exe).label Abort.threads.entry + Int64.ofNat 34 =
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .sys).pc := rfl
  have hsysT : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ.1
    subst hc0
    have hAc : ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s :=
      ac_stubA (by rw [hpc]; exact memSysT.1) hA hoff8 (.inr (.inr ⟨by rw [hpc]; exact memSysT.2, rfl⟩)) hJ.2
    rw [← he34] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o34)
    exact ⟨sfactsAC_svcT hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q34)
      (hown s _ σ hA hD) (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAc (hCl s),
      hP.2⟩
  have hsex : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, ⟨hc0, hra⟩, hax, hdi⟩
    change c = c0 at hc0
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.threads.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hAc : ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s :=
      ac_stubA (by rw [hpc]; exact memExT.1) hA hoff8 (.inr (.inr ⟨by rw [hpc]; exact memExT.2, rfl⟩)) hra
    have hx231 : σ.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ.regs.rdi.toNat) := by
      rw [← syscallCall_exitGroup hx231, syscallCall, ← hA.regs]; rfl
    refine ⟨sfactsAC_svcT hc (hc.place s hD) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.X64.Rt.cellOf hI hx (ofNat_zero' _) hs hn hpc)
      (Spike.Lib.X64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨hk k a ha (hpcN ▸ e), fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h) hAc (hCl s), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    simp only [Reg64s.get64] at hdi
    rw [← UInt64.toNat_toBitVec, hdi]; rfl
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 ∨ Abort.Disp.t1 = Abort.Disp.t5 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 ∨ Abort.Disp.t2 = Abort.Disp.t5 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 ∨ Abort.Disp.t3 = Abort.Disp.t5 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 ∨ Abort.Disp.t4 = Abort.Disp.t5 := .inr (.inr (.inr (.inl rfl)))
  have hT5 : Abort.Disp.t5 = Abort.Disp.t1 ∨ Abort.Disp.t5 = Abort.Disp.t2 ∨ Abort.Disp.t5 = Abort.Disp.t3 ∨
    Abort.Disp.t5 = Abort.Disp.t4 ∨ Abort.Disp.t5 = Abort.Disp.t5 := .inr (.inr (.inr (.inr rfl)))
  have hj : ∀ {blk : List (Directive × Nat)} {j : Nat},
      (blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3 ∨ blk = Abort.Disp.j4) →
      j < blk.length → j = 0 := by
    intro blk j hb hk
    rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, Abort.Disp.j4, List.length_zip, List.length_cons,
        List.length_nil] at hk <;> omega
  have hoD : Abort.Disp.oD.get .rbp = some 0 := by simp [SO.get, Spike.Lib.lk]
  have hoI : Abort.oI.get .rbp = some 0 := by simp [SO.get, Spike.Lib.lk]
  exact stubTW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_threadsAC hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispEA (memE5 hk) hA ((d0_run5 _ _ hk).1.trans hJ.2.1) hoff8
        (d0_run5 _ _ hk).2.2 ((d0_run5 _ _ hk).2.1.trans hJ.2.2))
    (blkW_threadsAC hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inl rfl) hT1 hk) hA (t_run5 hT1 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run5 hT1 _ _ hk).2).trans hJ.2.1) hoff8
        ((congrArg (fun f => f 8) (t_run5 hT1 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj1 rfl Abort.Disp.j1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inl rfl) hk
        exact ac_dispTA (memJ5 (.inl rfl) (.inl rfl) hk) hA hoD hoff hJ.2.1 hoff8 hJ.2.2)
    (blkW_threadsAC hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inl rfl)) hT2 hk) hA (t_run5 hT2 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run5 hT2 _ _ hk).2).trans hJ.2.1) hoff8
        ((congrArg (fun f => f 8) (t_run5 hT2 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj2 rfl Abort.Disp.j2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inl rfl)) hk
        exact ac_dispTA (memJ5 (.inr (.inl rfl)) (.inr (.inl rfl)) hk) hA hoD hoff hJ.2.1 hoff8 hJ.2.2)
    (blkW_threadsAC hI ht3 (ofNat_zero' _) Abort.Disp.t3_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run5 hT3 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run5 hT3 _ _ hk).2).trans hJ.2.1) hoff8
        ((congrArg (fun f => f 8) (t_run5 hT3 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj3 rfl Abort.Disp.j3_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inr (.inl rfl))) hk
        exact ac_dispTA (memJ5 (.inr (.inr (.inl rfl))) (.inr (.inr (.inl rfl))) hk) hA hoD hoff hJ.2.1 hoff8
          hJ.2.2)
    (blkW_threadsAC hI ht4 (ofNat_zero' _) Abort.Disp.t4_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inl rfl)))) hT4 hk) hA (t_run5 hT4 _ _ hk).1 hoff
          ((congrArg (fun f => f (-8)) (t_run5 hT4 _ _ hk).2).trans hJ.2.1) hoff8
          ((congrArg (fun f => f 8) (t_run5 hT4 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj4 rfl Abort.Disp.j4_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inr (.inr rfl))) hk
        exact ac_dispTA (memJ5 (.inr (.inr (.inr rfl))) (.inr (.inr (.inr rfl))) hk) hA hoD hoff hJ.2.1 hoff8
          hJ.2.2)
    (blkW_threadsAC hI ht5 (ofNat_zero' _) Abort.Disp.t5_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inr rfl)))) hT5 hk) hA (t_run5 hT5 _ _ hk).1 hoff
          ((congrArg (fun f => f (-8)) (t_run5 hT5 _ _ hk).2).trans hJ.2.1) hoff8
          ((congrArg (fun f => f 8) (t_run5 hT5 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hg5 (ofNat_zero' _) Abort.Disp.g5_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pg5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_g5A (memG5 hk) hA hoff8 (g5_run _ _ hk).2 ((g5_run _ _ hk).1.trans hJ.2))
    (blkW_threadsAC hI hb0 (ofNat_zero' _) Abort.x0_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_stubA (memX0T hk) hA hoff8 (x0_run5 _ _ hk).2 ((x0_run5 _ _ hk).1.trans hJ.2))
    (nodeW_si_threadsAC (si := Abort.siMsg Abort.threads) hI hn1 rfl (ofNat_zero' _).symm o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun _ _ _ hJ hA h => ac_stubA (by rw [h, ofNat_zero']; exact memN1T.1) hA hoff8
        (.inr (.inr ⟨by rw [h, ofNat_zero']; exact memN1T.2, hoI⟩)) hJ.2)
    (blkW_threadsAC hI hb1 rfl Abort.x1Threads_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_stubA (memX1T hk).1 hA hoff8 (.inr (.inr ⟨(memX1T hk).2, (x1T_run _ _ hk).1⟩))
        ((x1T_run _ _ hk).2.trans hJ.2))
    hsysT
    (blkW_threadsAC hI hb2 rfl Abort.x2_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_stubA (memX2T hk).1 hA hoff8 (.inr (.inr ⟨(memX2T hk).2, (x2_run5 _ _ hk).1⟩))
        ((x2_run5 _ _ hk).2.trans hJ.2))
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

end Spike.Lib.X64.StubW

/-- info: 'Spike.Lib.X64.StubW.sfactsAC_doneT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.sfactsAC_doneT

/-- info: 'Spike.Lib.X64.StubW.sfactsAC_svcT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.sfactsAC_svcT

/-- info: 'Spike.Lib.X64.StubW.ac_g5A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.ac_g5A

/-- info: 'Spike.Lib.X64.StubW.ac_stubA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.ac_stubA

/-- info: 'Spike.Lib.X64.StubW.blkW_threadsAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.blkW_threadsAC

/-- info: 'Spike.Lib.X64.StubW.nodeW_si_threadsAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.nodeW_si_threadsAC

/-- info: 'Spike.Lib.X64.StubW.seg_svcTW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.seg_svcTW

/-- info: 'Spike.Lib.X64.StubW.stubTW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.stubTW_of_code

/-- info: 'Spike.Lib.X64.StubW.stubTW_sfactsAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.stubTW_sfactsAC
