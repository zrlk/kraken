/-
**The heap abort path's obligations inside `SFactsA`** (x86-64): the
`Abort.Disp.StubHW` of a jump to `scc_rt_abort` with `%rdi = 2`
(`Spike/Lib/X64AbortHeapW.lean`) at `W := SFactsA … frs Dt` with no abort
phase (`Spike/Lib/X64SegInstA.lean`), for any program with the abort code
(`Scc.Cert.Rt.X64.Abort.abortIn`), an instance's facts at the frames `frs`
(`InstOk` at `own · frs`, `Spike/Lib/Rt/X64RtW.lean`) and the path's phase
check (`abortPhHeapOk`, `Spike/Lib/X64AbortPhH.lean`). The twin of
`Spike/Lib/A64StubHA.lean`.

The source control `c0` is the allocation the arena cannot serve: it is at
a `newBuf` (`AtNewBuf`), so no frame run leaves it (`FrameRun.eq_of_stuck`)
and the per-pair facts at the frame runs from it are the facts at `(c0, frs)`.

* `NbCtl`: the facts of `c0` the path needs (at a `newBuf`, its type passing
  the zero check, placed at every memory of the frame condition, a frame run
  into it keeping the owned words);
* `run_eq`: a frame run from a `newBuf` is empty;
* `sfactsA_done`, `sfactsA_sys`: `SFactsA` at an instruction without an
  event off the sites, and at a `syscall` with the abort facts and the write
  tail given;
* `blkW_heapA`, `nodeW_si_heapA`: a block and a single instruction of the
  path (as `blkW_ovf`, `nodeW_si_ovf`, `Spike/Lib/X64StubW.lean`);
* `stubHW_sfactsA`: `StubHW` inside `SFactsA … frs Dt`, the write tail `Dt`
  holding at the stub's `write` (`hwr`), the exit call the heap abort site
  with `HeapAbortObl` at `c0` (`hobl`).

**Unlike AArch64**: instructions have sizes (a block's pcs are its label's
plus `cellOff`); `ownSys` also covers `arch_prctl`'s resumed state; the
region asks 8-alignment only; the stub's region is `[-24, 16)` from its
frame base.
-/
import Spike.Lib.X64AbortPhH
import Spike.Lib.X64AbortStubCode
import Spike.Lib.X64SegInstA

namespace Spike.Lib.X64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf abi atSyscall_of_cellAt atSyscall_false_of_cellAt mem_certSuccs_syscall
  certSuccs_archSetFs)
open Spike.Lib.Consumer1 (allInv_true)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerS (OwnS PlacedS)
open Spike.Lib.X64ConsumerA
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (StackOff stackOff_stable)
open Spike.Lib.X64.Rt (InstOk owned_off)
open Scc.Cert.Rt.X64 (blockAtB code_field)
open Kraken.Promising.Lower.X64 (op64)

/-! ## The control at the allocation -/

/-- **The facts of the control at the failing allocation** at the frames
`frs`: at a `newBuf`, its type passing the zero check, placed at every
memory of the frame condition `F`, and every frame run into it keeping the
owned words (`SFactsA.ownRun`'s second case; its first is `run_eq`). -/
structure NbCtl (Λ : Scc.Sem.Layout) (p : Prog) (own : OwnS) (lbl : Lbl) (F : MachineData → Prop) (c0 : Ctl)
    (frs : List TermRun.Frame) : Prop where
  nb : AtNewBuf c0
  zero : ∀ x a τ e, c0.term = .let_ x (.newBuf a τ) e → ZeroOkTy τ = true
  place : ∀ s : State, F s.st.1 → PlacedS Λ lbl s c0 frs
  runIn : ∀ (s : State) c₁ fs₁, FrameRun p (c₁, fs₁) (c0, frs) → own s frs = own s fs₁

/-- **A frame run from a `newBuf` is empty.** -/
theorem run_eq {p : Prog} {c c' : Ctl} {fs fs' : List TermRun.Frame} (hnb : AtNewBuf c)
    (h : FrameRun p (c, fs) (c', fs')) : c' = c ∧ fs' = fs := by
  have := FrameRun.eq_of_stuck h (.inl hnb)
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## `SFactsA` at one state -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt : State → Prop}

open Kraken.Promising.Lower.X64 (CellAt after)

/-- **`SFactsA` at an instruction without an event** (not a `syscall`, its
step `.done s'`), off the marks' sites, at a control at a `newBuf`: the
leaf owns what `s` owns and is in the phase iff `s` is; in the phase the
range is owned. -/
theorem sfactsA_done {s' : State} {d : Directive} {sz : Nat} (hnb : AtNewBuf c)
    (hz : ∀ x a τ e, c.term = .let_ x (.newBuf a τ) e → ZeroOkTy τ = true) (hpl : PlacedS Λ lbl s c fs)
    (hin : ∀ c₁ fs₁, FrameRun p (c₁, fs₁) (c, fs) → own s fs = own s fs₁) (hP : PcOff μ s)
    (hc : CellAt s d sz) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec s = some (.done s'))
    (hown : own s' fs = own s fs) (htk : Tk s' ↔ Tk s) (hO : Tk s → Owned Λ rS s) :
    SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) := by
  have hs : abi.atSys s = false := atSyscall_false_of_cellAt hc hd
  obtain ⟨x0, a0, τ0, e0, ht⟩ := id hnb
  refine
    { noRet := fun _ a h => by rw [ht] at h; cases h
      cell := fun c' fs' hr x a e ty w h => by
        obtain ⟨rfl, -⟩ := run_eq hnb hr
        rcases h with h | ⟨b, h⟩ <;> rw [ht] at h <;> cases h
      noSite := hP.noSite
      mapped := fun _ e he => by rw [hex] at he; cases he; nofun
      place := .of_placedS hpl
      svc := fun h => by rw [hs] at h; cases h
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := run_eq hnb hr
          rfl
        · exact hin c₁ fs₁ hr
      ownInstr := fun c' fs' hr _ tree he => by
        obtain ⟨rfl, rfl⟩ := run_eq hnb hr
        rw [hex] at he; cases he
        exact .inl ⟨hown, trivial⟩
      ownSys := fun _ _ _ h => by rw [hs] at h; cases h
      ownTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      site := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkInstr := fun _ _ tree he => by rw [hex] at he; cases he; exact htk
      tkSys := fun h => by rw [hs] at h; cases h
      owned := hO
      wrTail := fun h => by rw [hs] at h; cases h
      wr := fun _ _ _ _ => wrOkA_of_noWr (noWr_done hex)
      zero := fun c' fs' hr => by
        obtain ⟨rfl, -⟩ := run_eq hnb hr
        exact hz
      abortOk := fun k a ha hpc => (hP.noAbort k a ha hpc).elim
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false }

/-- **`SFactsA` at a `syscall`** of `z` bytes off the release and take
sites, at a control at a `newBuf`, with the heap abort facts (`hab`) and
the write tail (`hwr`) given: every state the kernel resumes in is past it,
owning what `s` owns and in the phase iff `s` is. -/
theorem sfactsA_sys {z : Nat} (hnb : AtNewBuf c)
    (hz : ∀ x a τ e, c.term = .let_ x (.newBuf a τ) e → ZeroOkTy τ = true)
    (hpl : PlacedS Λ lbl s c fs) (hin : ∀ c₁ fs₁, FrameRun p (c₁, fs₁) (c, fs) → own s fs = own s fs₁)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hc : CellAt s (op64 .syscall) z)
    (hnext : ∀ m, own (after s z m) fs = own s fs ∧ (Tk (after s z m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c) ∧
      ∀ v, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) →
        v % 256 = Scc.Sem.Kernel.abortStatus)
    (hwr : ∀ fd buf n, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s) :
    SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) := by
  have hs : abi.atSys s = true := atSyscall_of_cellAt hc
  have hsucc : ∀ call, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call, own s' fs = own s fs ∧ (Tk s' ↔ Tk s) := by
    intro call _ s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | head => exact hnext _
      | tail _ h => cases h
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      exact hnext _
  obtain ⟨x0, a0, τ0, e0, ht⟩ := id hnb
  refine
    { noRet := fun _ a h => by rw [ht] at h; cases h
      cell := fun c' fs' hr x a e ty w h => by
        obtain ⟨rfl, -⟩ := run_eq hnb hr
        rcases h with h | ⟨b, h⟩ <;> rw [ht] at h <;> cases h
      noSite := hrel
      mapped := fun h => by rw [hs] at h; cases h
      place := .of_placedS hpl
      svc := fun _ => ⟨z, hc⟩
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := run_eq hnb hr
          rfl
        · exact hin c₁ fs₁ hr
      ownInstr := fun _ _ _ h => by rw [hs] at h; cases h
      ownSys := fun c' fs' hr _ call hd s' hs' => by
        obtain ⟨rfl, rfl⟩ := run_eq hnb hr
        exact (hsucc call hd s' hs').1
      ownTake := fun a ha hpc => (htake a ha hpc).elim
      site := fun a ha hpc => (htake a ha hpc).elim
      tkTake := fun a ha hpc => (htake a ha hpc).elim
      tkInstr := fun _ h => by rw [hs] at h; cases h
      tkSys := fun _ call hd s' hs' => (hsucc call hd s' hs').2
      owned := hO
      wrTail := fun _ => hwr
      wr := fun _ _ _ h => by rw [hs] at h; cases h
      zero := fun c' fs' hr => by
        obtain ⟨rfl, -⟩ := run_eq hnb hr
        exact hz
      abortOk := fun k a ha hpc => let ⟨h1, h2⟩ := hab k a ha hpc; ⟨.inr (.inr h1), h2⟩
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false }

end State

/-! ## The path's blocks and single instructions -/

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop}

/-- **A block of the heap abort path inside `SFactsA`** at the frames
`frs`: its code (`hb`), its phase check without dead targets (`hph`), no
`ret` (`hnr`), the source control `c0` at every state (`hJ`) with its facts
(`hc`); the words of `rS` off the region in the frame condition (`hFO`). -/
theorem blkW_heapA {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {off : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat off) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : NbCtl Λ p own lbl F c0 frs) :
    BlkW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False)) K exe endPc R F
      n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  rw [he, ← hI.labOk] at hph
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
  intro s σ c hs hn _ _ hA hD hJc k hk m hA' hDm
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
  exact sfactsA_done hc.nb hc.zero (hc.place _ (hF _ _ hD hDm)) (hc.runIn _) hP hcell (AI.not_syscall hreg) hex
    hown htk fun _ => owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hD) hDm)
      fun k' hk' => Option.isSome_iff_exists.mpr (by obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩)

/-- **A single instruction without an event (`SI`) of the heap abort path
inside `SFactsA`**: off the sites (`hok`), its next pc in its phase
(`hph`), the source control as in `blkW_heapA`. -/
theorem nodeW_si_heapA {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {si : SI} {l : Label} {off z : Nat} {q : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off [(si.toDir, z)] = true) (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (hok : okPc q.toBitVec.toNat = true) (hph : ph (q + Int64.ofNat z).toBitVec.toNat = ph q.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : NbCtl Λ p own lbl F c0 frs) :
    NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False)) K exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJc⟩
  obtain rfl := hJ σ c hJc
  rw [hp] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  have hcell := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hnx := Spike.Lib.X64.Rt.next_same hI hpc hph
  refine ⟨sfactsA_done hc.nb hc.zero (hc.place s hD) (hc.runIn s) hP.1 hcell
    (by cases si <;> intro w w' h <;> cases h) (exec_si hcell) (hnx _).1 (hnx _).2
    fun _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => ?_, hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

end Nodes

/-! ## `StubHW` (the phase check `abortPhHeapOk` in `Spike/Lib/X64AbortPhH.lean`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **The heap abort path's obligations inside `SFactsA … frs Dt`**
(`Abort.Disp.StubHW`, no abort phase), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`). The callee's region holds the stub's frame (`hlo`,
`hhi`); the words of `rS` lie off it in the frame condition (`hFO`); the
source control `c0` is the failing allocation (`hc`). The exit call is the
heap abort site: off the release and take sites (`hrel`, `htk`), no other
kind's (`hk`), `c0` with the heap abort's obligation there (`hobl`), no
outside move (`hKex`), the memory side's abort (`hms`). The write tail
`Dt` holds at the `write` (`hwr`). -/
theorem stubHW_sfactsA {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop}
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhHeapOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : NbCtl Λ p own lbl F c0 frs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.heap.exit).toBitVec.toNat = a → k = .heap)
    (hKex : ∀ s s', pcOf s = (lab Abort.heap.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.heap.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.heap c0 .sys) s c → Dt s) :
    Abort.Disp.StubHW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False))
      K p al ms exe endPc R F c0 := by
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.1.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hb1, hsysIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, q1, pb1, o5, q5, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he34 : (_root_.Executable.labels exe).label Abort.heap.entry + Int64.ofNat 34 =
      (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .sys).pc := rfl
  have hsysW : NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False)) K exe
      endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ
    subst hc0
    rw [← he34] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o5)
    exact ⟨sfactsA_sys hc.nb hc.zero (hc.place s hD) (hc.runIn s) hP.1.noSite hP.1.noTake
      (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q5) (hown s _ σ hA hD)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt), hP.2⟩
  have hsex : NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False)) K exe
      endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJ, hax, hdi⟩
    have hc0 : c = c0 := hJ
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.heap.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hx231 : σ.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ.regs.rdi.toNat) := by
      rw [← syscallCall_exitGroup hx231, syscallCall, ← hA.regs]; rfl
    refine ⟨sfactsA_sys hc.nb hc.zero (hc.place s hD) (hc.runIn s) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.X64.Rt.cellOf hI hx (ofNat_zero' _) hs hn hpc)
      (Spike.Lib.X64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨⟨hk k a ha (hpcN ▸ e), hobl⟩, fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    simp only [Reg64s.get64] at hdi
    rw [← UInt64.toNat_toBitVec, hdi]; rfl
  exact stubHW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_heapA hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc)
    (blkW_heapA hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc)
    (blkW_heapA hI hj1 rfl Abort.Disp.j1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc)
    (blkW_heapA hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc)
    (blkW_heapA hI hg2 (ofNat_zero' _) Abort.Disp.g2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pg2 rfl (fun _ _ h => h) hc)
    (blkW_heapA hI hb0 (ofNat_zero' _) Abort.x0_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h) hc)
    (nodeW_si_heapA (si := Abort.siMsg Abort.heap) hI hn1 rfl (ofNat_zero' _).symm o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h) hc)
    (blkW_heapA hI hb1 rfl Abort.x1Heap_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h) hc)
    hsysW
    (blkW_heapA hI hb2 rfl Abort.x2_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h) hc)
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

end Spike.Lib.X64.StubW
