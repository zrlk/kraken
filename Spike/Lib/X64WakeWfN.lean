/-
**wake.w's pre-clone states at its nodes** (`Wf`, x86-64; twin of `Spike/Lib/A64WakeWfN.lean`): a node's or a
block's obligation inside `Wf` (`Spike/Lib/X64WakeWf.lean`) at a fixed
frame list, from its components, and the components at the common node
kinds. Generic in the layout, the marks, the owned words, the arena, the
phases and the clone path: no layout constant, no placement.

- `Wf.intro`, `W0.intro`, `W0.intro0`, `noRet_cons`: `Wf`/`W0` from the
  components.
- `nodeW_wf`, `blkW_wf`: a node or block inside `Wf` from one inside
  `SFactsSt2` (moved by `K`) and ones inside the other components (no
  outside moves); the clone clause is global (`hcl`, `clW_svc` at `clW`).
- `NoWrC`, `noWrC_of_noWr`, `nodeW_noWrC`, `blkW_noWrC`: a state writing
  nothing has `ArenaWr` and the counter clause at every frame list; at a
  silent node or block (`nodeW_noWr_si`, `blkW_noWr`) and at a `syscall`
  (`nodeW_noWr_svc`).
- `nodeW_wrC_st`: a store to a word off the arena and the counter (a frame
  slot, a TCB word) has them (`nodeW_wr_st`).
- `abortWf_of_off`, `nodeW_abortWf_off`: `AbortWf` off the abort sites.
- `nodeW_abSt_svc`, `nodeW_acSt_svc`: the phases kept at an `svc` whose
  resumed states are out of them (at `Ac`, or at the clone path `Cl`).
- `RunWf.ofRunOk`, `RunWf.ofRunOk2`, `RunWf.run`: the source's runs.

**Unlike AArch64**: the system call is `syscall` (a cell of size `z`, its
resumed state `sysRet s z r`, AArch64's `svcRet s 4 r`); `nodeW_abSt_svc`,
`nodeW_acSt_svc` take `hna` (no `arch_prctl` at the node: its resumed state
sets the thread pointer first, `certSuccs_archSetFs`); `nodeW_wrC_st` is at
x86-64's store `stDir b k r` (`blockAtB` at a byte offset).
-/
import Spike.Lib.X64WakeWf
import Spike.Lib.X64AllocG
import Spike.Lib.X64Hello1SFactsN
import Spike.Lib.Src.RunOk2

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS Frag Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt bAddr stDir)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt op64 exec_syscall syscallRet syscallInfo)

/-- **The state a `syscall` cell of size `z` resumes in**, returning `r`
(AArch64's `svcRet s 4 r`). -/
abbrev sysRet (s : State) (z : Nat) (r : BitVec 64) : State :=
  syscallRet s z (kret (rflags s.st.1.status) (syscallInfo s z) r)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}

/-! ## `Wf` from its components -/

/-- **`Wf` from its components** (the clone clause from the global `hcl`). -/
theorem Wf.intro {s : State} {c : Ctl} {fs : List TermRun.Frame} (hst : SFactsSt2 Λ μ own s Dt)
    (hab : AbSt μ Ab s) (hac : AcSt μ Cl Ac s)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hnr : fs = [] → ∀ a, c.term ≠ .ret a) (hpl : PlacedSE Λ lbl s c fs) (har : ArenaWr ar p lbl lsize Ctx s c fs)
    (hcx : WrAt s ar.ctrLoc → Ctx s c fs) (hr : RunWf p c fs) (habt : AbortWf ar μ Ab Ac s c fs) :
    Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs :=
  ⟨hst, hab, hac, hcl s, hnr, hpl, har, hcx, hr, habt⟩

/-- No `ret` of `main` at no frame, at a nonempty frame list. -/
theorem noRet_cons {c : Ctl} {f : TermRun.Frame} {fs : List TermRun.Frame} :
    f :: fs = [] → ∀ a, c.term ≠ .ret a := fun h => absurd h (List.cons_ne_nil _ _)

/-- **`W0` from `Wf`** at the frames `[frM]`, the per-state facts `X0`. -/
theorem W0.intro {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {s : State} {c : Ctl}
    (hx : X0 s) (h : Wf Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 s c [frM]) :
    W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c [frM] :=
  ⟨.inr rfl, hx, h⟩

/-- **`W0` from `Wf`** at no frames (the start), the per-state facts `X0`. -/
theorem W0.intro0 {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {s : State} {c : Ctl}
    (hx : X0 s) (h : Wf Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 s c []) :
    W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c [] :=
  ⟨.inl rfl, hx, h⟩

/-! ## Node and block obligations from the components -/

section Lift

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {K : State → State → Prop}
  {fs : List TermRun.Frame}

/-- **A node inside `Wf`** at the frames `fs` from its components: the
state's facts (moved by `K`), the phases, the control's facts, the arena's
writes, the counter clause and the abort sites (no outside moves). -/
theorem nodeW_wf {n : ND} (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n)
    (hac : NodeW (fun s _ => AcSt μ Cl Ac s) (fun _ _ => False) exe endPc R F n)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : NodeW (fun s c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedSE Λ lbl s c fs ∧ RunWf p c fs)
      (fun _ _ => False) exe endPc R F n)
    (hwr : NodeW (fun s c => ArenaWr ar p lbl lsize Ctx s c fs ∧ (WrAt s ar.ctrLoc → Ctx s c fs))
      (fun _ _ => False) exe endPc R F n)
    (habt : NodeW (fun s c => AbortWf ar μ Ab Ac s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs) K exe endPc R F n := fun s c hA =>
  let ⟨hnr, hpl, hr⟩ := (hctl s c hA).1
  ⟨Wf.intro (hst s c hA).1 (hab s c hA).1 (hac s c hA).1 hcl hnr hpl (hwr s c hA).1.1 (hwr s c hA).1.2 hr
    (habt s c hA).1, (hst s c hA).2⟩

/-- **A block node inside `Wf`** at the frames `fs` from its components
(as `nodeW_wf`). -/
theorem blkW_wf {n : ND} {blk : List (Directive × Nat)}
    (hst : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hac : BlkW (fun s _ => AcSt μ Cl Ac s) (fun _ _ => False) exe endPc R F n blk)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : BlkW (fun s c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedSE Λ lbl s c fs ∧ RunWf p c fs)
      (fun _ _ => False) exe endPc R F n blk)
    (hwr : BlkW (fun s c => ArenaWr ar p lbl lsize Ctx s c fs ∧ (WrAt s ar.ctrLoc → Ctx s c fs))
      (fun _ _ => False) exe endPc R F n blk)
    (habt : BlkW (fun s c => AbortWf ar μ Ab Ac s c fs) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs) K exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    let r := hst s σ c he hn hd hp hA hF hJ k hk m hA' hD
    let ⟨hnr, hpl, hr⟩ := (hctl s σ c he hn hd hp hA hF hJ k hk m hA' hD).1
    let w := (hwr s σ c he hn hd hp hA hF hJ k hk m hA' hD).1
    ⟨Wf.intro r.1 (hab s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (hac s σ c he hn hd hp hA hF hJ k hk m hA' hD).1
      hcl hnr hpl w.1 w.2 hr (habt s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, r.2⟩

end Lift

/-! ## The writes -/

/-- **The arena's writes and the counter clause** at the frames `fs`. -/
def NoWrC (ar : Arena) (p : Prog) (lbl : Lbl) (lsize : Lsize) (Ctx : FragS isa) (fs : List TermRun.Frame) :
    Frag isa := fun s c =>
  ArenaWr ar p lbl lsize Ctx s c fs ∧ (WrAt s ar.ctrLoc → Ctx s c fs)

/-- A state writing nothing has `NoWrC` at every frame list. -/
theorem noWrC_of_noWr {s : State} {c : Ctl} (h : ∀ L, ¬ WrAt s L) (fs : List TermRun.Frame) :
    NoWrC ar p lbl lsize Ctx fs s c :=
  ⟨fun _ _ _ L hL => (h L hL).elim, fun hL => (h _ hL).elim⟩

/-- A state whose writes are off the arena and the counter has `NoWrC`. -/
theorem noWrC_of_off {s : State} {c : Ctl}
    (h : ∀ L, WrAt s L → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) ∧ L ≠ ar.ctrLoc)
    (fs : List TermRun.Frame) : NoWrC ar p lbl lsize Ctx fs s c :=
  ⟨fun _ _ _ L hL _ => .inl (.inr (.inl (h L hL).1)), fun hL => ((h _ hL).2 rfl).elim⟩

section Wr

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}

/-- **A node writing nothing** has `NoWrC`. -/
theorem nodeW_noWrC {n : ND} (h : NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := fun s c hA =>
  ⟨noWrC_of_noWr (h s c hA).1 fs, (h s c hA).2⟩

/-- **A block writing nothing** has `NoWrC`. -/
theorem blkW_noWrC {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    ⟨noWrC_of_noWr (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 fs,
      (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩

/-- **A `syscall` writes nothing**: its tree is a fault (`exec_syscall`). -/
theorem nodeW_noWr_svc {n : ND} {z : Nat}
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)]) :
    NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hcell : CellAt s (op64 .syscall) z := (hc s hs hn).cell0 rfl rfl hpc
  refine ⟨fun L hL => ?_, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [exec_syscall hcell] at h <;> cases h

variable [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {lab : Label → Int64} {μ' : Marks}
  {own' : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store** `movq %r, k(%b)` of a word unmapped in private memory
(`ha`), off the arena and not the counter word (`hoff`: a frame slot, a TCB
word), has `NoWrC` (`AllocG.nodeW_wr_st`). -/
theorem nodeW_wrC_st (hI : InstOk exe endPc cells lab μ' own' Tk K okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {q : Int64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b k).toNat ∧ (bAddr σ.regs b k).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b k, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := fun s c hA =>
  let ⟨σ, hJ, hF, hw⟩ := (Spike.Lib.X64.AllocG.nodeW_wr_st hI hb he hp ha s c hA).1
  ⟨noWrC_of_off (fun L hL => hw L hL ▸ hoff σ c s.st.1 hJ hF) fs, fun _ h => h⟩

end Wr

/-! ## The abort sites -/

/-- **`AbortWf` off every abort site.** -/
theorem abortWf_of_off {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a) : AbortWf ar μ Ab Ac s c fs :=
  fun k a ha hpc => (h k a ha hpc).elim

/-- **A node off every abort site** has `AbortWf` at every frame list. -/
theorem nodeW_abortWf_off {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {fs : List TermRun.Frame} (h : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a) :
    NodeW (fun s c => AbortWf ar μ Ab Ac s c fs) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, hpc, -⟩
  exact ⟨abortWf_of_off fun k a ha => by unfold pcOf; rw [hpc]; exact h k a ha, fun _ h => h⟩

/-! ## The phases at an `svc` -/

section Svc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The write abort's phase kept at a `syscall`** off the take site
(`htk`), at no `arch_prctl` (`hna`), whose every resumed state is out of
`Ab` (`hout`). -/
theorem nodeW_abSt_svc {n : ND} {z : Nat}
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (hna : ∀ s c, At exe endPc R F n s c → ∀ a, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.archSetFs a))
    (hout : ∀ s c, At exe endPc R F n s c → ∀ r, ¬ Ab (sysRet s z r)) :
    NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -⟩ := id hA
  have hcell : CellAt s (op64 .syscall) z := (hc s hs hn).cell0 rfl rfl hpc
  refine ⟨⟨fun _ h => ?_, fun _ _ call hd s' hs' hab => ?_, fun _ a ha hpc' => ?_⟩, fun _ h => h⟩
  · rw [show abi.atSys s = true from atSyscall_of_cellAt hcell] at h; cases h
  · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hcell fun a he => hna s c hA a (he ▸ hd)).mp hs'
    exact (hout s c hA r hab).elim
  · exact (htk a ha (by unfold pcOf at hpc'; rw [hpc] at hpc'; exact hpc')).elim

/-- **The threads abort's phase kept at a `syscall`** off the take site
(`htk`), at no `arch_prctl` (`hna`): at the clone path `Cl`, or every
resumed state out of `Ac` (`hout`). -/
theorem nodeW_acSt_svc {n : ND} {z : Nat}
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (hna : ∀ s c, At exe endPc R F n s c → ∀ a, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.archSetFs a))
    (hout : ∀ s c, At exe endPc R F n s c → Cl s ∨ ∀ r, ¬ Ac (sysRet s z r)) :
    NodeW (fun s _ => AcSt μ Cl Ac s) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -⟩ := id hA
  have hcell : CellAt s (op64 .syscall) z := (hc s hs hn).cell0 rfl rfl hpc
  refine ⟨⟨fun _ h => ?_, fun _ _ hncl call hd s' hs' hac => ?_, fun _ a ha hpc' => ?_⟩, fun _ h => h⟩
  · rw [show abi.atSys s = true from atSyscall_of_cellAt hcell] at h; cases h
  · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hcell fun a he => hna s c hA a (he ▸ hd)).mp hs'
    exact (hout s c hA).elim (fun h => hncl h) fun h => h r hac
  · exact (htk a ha (by unfold pcOf at hpc'; rw [hpc] at hpc'; exact hpc')).elim

end Svc

/-! ## The source's runs -/

/-- `RunWf` is hello1's `RunOk`. -/
theorem RunWf.ofRunOk {c : Ctl} {fs : List TermRun.Frame} (h : Spike.Lib.X64.Flow.Hello1.SFactsN.RunOk p c fs) :
    RunWf p c fs :=
  ⟨h.cell, h.zero⟩

/-- `RunWf` is the lowering's `RunOk2`. -/
theorem RunWf.ofRunOk2 {c : Ctl} {fs : List TermRun.Frame} (h : Spike.Lib.LowerNode.RunOk2 p c fs) :
    RunWf p c fs :=
  ⟨h.cell, h.zero⟩

/-- `RunWf` along a frame run. -/
theorem RunWf.run {c c₁ : Ctl} {fs fs₁ : List TermRun.Frame} (h : RunWf p c fs)
    (hr : FrameRun p (c, fs) (c₁, fs₁)) : RunWf p c₁ fs₁ :=
  ⟨fun _ _ hr' => h.cell _ _ (hr.trans hr'), fun _ _ hr' => h.zero _ _ (hr.trans hr')⟩

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wf

/-- info: 'Spike.Lib.X64.WakeWf.blkW_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_wf

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wrC_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wrC_st

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_noWr_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_noWr_svc

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_abSt_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_abSt_svc

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_acSt_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_acSt_svc

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_abortWf_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_abortWf_off

/-- info: 'Spike.Lib.X64.WakeWf.Wf.intro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.Wf.intro

/-- info: 'Spike.Lib.X64.WakeWf.noRet_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.noRet_cons

/-- info: 'Spike.Lib.X64.WakeWf.W0.intro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.W0.intro

/-- info: 'Spike.Lib.X64.WakeWf.W0.intro0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.W0.intro0

/-- info: 'Spike.Lib.X64.WakeWf.noWrC_of_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.noWrC_of_noWr

/-- info: 'Spike.Lib.X64.WakeWf.noWrC_of_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.noWrC_of_off

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_noWrC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_noWrC

/-- info: 'Spike.Lib.X64.WakeWf.blkW_noWrC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_noWrC

/-- info: 'Spike.Lib.X64.WakeWf.abortWf_of_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.abortWf_of_off

/-- info: 'Spike.Lib.X64.WakeWf.RunWf.ofRunOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.RunWf.ofRunOk

/-- info: 'Spike.Lib.X64.WakeWf.RunWf.ofRunOk2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.RunWf.ofRunOk2

/-- info: 'Spike.Lib.X64.WakeWf.RunWf.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.RunWf.run
