/-
**wake.w's writing nodes inside `Wf`** (x86-64; twin of
`Spike/Lib/A64WakeWfW.lean`): the per-node obligation of `Wf`
(`Spike/Lib/X64WakeWf.lean`) at a store `movq %r, k(%b)` or an RMW
(`lock xaddq %r, k(%b)`, `xchgq %r, k(%b)`) of a word unmapped in private
memory, off the arena and not the counter word (a runtime word:
`scc_rt_pinned_next`, a TCB header, the stack lock), as
`WakeWf.nodeW_wfQ` for the quiet ones: the state's facts (`SFactsSt2`,
moved by `K`), one decided phase check (`siOff`), the control's facts at
the node's invariant and the frames placed. Generic in the layout, the
marks, the owned words, the arena and the clone path.

- `st_step`, `xadd_step`, `xchg_step`: the instruction's one step to
  `pc + z`, not a `syscall` (`nodeW_phSt`'s `hstep`).
- `noWrC_of_only`: a state writing one word off the arena and the counter.
- `nodeW_wrC_xadd`, `nodeW_wrC_xchg`: an RMW's `NoWrC` (`nodeW_wrC_st`
  for the RMW).
- `nodeW_wfSt`, `nodeW_wfXadd`, `nodeW_wfXchg`: the store's and the RMWs'
  states inside `Wf` at the frames `fs`.

**Unlike AArch64**: AArch64's one RMW `ld<op> Xs, Xt, [Xn]` (`ldop_step`,
`nodeW_wrC_ldop`, `nodeW_wfLdop`, covering `ldadd` and `swp`) is two
x86-64 instructions, `lock xaddq` (the counters) and `xchgq` (the stack
lock), each with its own `_step`, `nodeW_wrC_` and `nodeW_wf` lemma; every
instruction sits at a byte offset `k` of a label (`blockAtB`) and has a
size `z` (`siOff … z`); the address is `bAddr σ.regs b k`, AArch64's
`rAddr σ.regs b i` (the RMW at `k(%b)`, AArch64's at `[Xn]`).
-/
import Spike.Lib.X64WakeWfG

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW ND At stDir xaddDir xchgDir bAddr mB eaddr_mB)
open Spike.Lib.X64.Rt (InstOk cellOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_store_agrees exec_xaddG_agrees exec_xchg access_agrees)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ' : Marks} {own' : Own} {Tk : State → Prop}
  {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-! ## The steps -/

/-- **A store of an unmapped word steps to `pc + z`**, its cell not a
`syscall`. -/
theorem st_step (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
    {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(stDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧ (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  refine ⟨_, _, hc, fun w w' h => (by cases h),
    exec_store_agrees hc ha' (ha σ c s.st.1 hJ hF) (Spike.Lib.X64.agrees_of_decls hdc _ _), fun s' hu => ?_⟩
  simp only [TreeLeaf] at hu
  obtain ⟨_, rfl⟩ := hu; rfl

/-- **A `lock xaddq` of an unmapped word steps to `pc + z`**, its cell not
a `syscall`. -/
theorem xadd_step (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
    {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(xaddDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧ (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  refine ⟨_, _, hc, fun w w' h => (by cases h),
    exec_xaddG_agrees (w := .W64) hc ha' (ha σ c s.st.1 hJ hF) (Spike.Lib.X64.agrees_of_decls hdc _ _),
    fun s' hu => ?_⟩
  simp only [TreeLeaf] at hu
  obtain ⟨_, rfl⟩ := hu; rfl

/-- **An `xchgq` of an unmapped word steps to `pc + z`**, its cell not a
`syscall`. -/
theorem xchg_step (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
    {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(xchgDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧ (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  refine ⟨_, _, hc, fun w w' h => (by cases h), exec_xchg hc ha' (ha σ c s.st.1 hJ hF), fun s' hu => ?_⟩
  rw [access_agrees (Spike.Lib.X64.agrees_of_decls hdc _ _)] at hu
  simp only [TreeLeaf] at hu
  obtain ⟨_, rfl⟩ := hu
  rfl

/-! ## The writes -/

omit [Kraken.Executable.ValidLayout exe] in
/-- A state writing only `L0`, off the arena and not the counter word, has
`NoWrC`. -/
theorem noWrC_of_only {s : State} {c : Ctl} {L0 : Loc} (hw : ∀ L, WrAt s L → L = L0)
    (hoff : ¬ (ar.heap ≤ L0.addr.toNat ∧ L0.addr.toNat < ar.heap + 16 * ar.cells) ∧ L0 ≠ ar.ctrLoc) :
    NoWrC ar p lbl lsize Ctx fs s c :=
  noWrC_of_off (fun L hL => hw L hL ▸ hoff) fs

/-- **A `lock xaddq %r, k(%b)`** of a word unmapped in private memory
(`ha`), off the arena and not the counter word (`hoff`), has `NoWrC`
(`AllocG.nodeW_wr_xadd`). -/
theorem nodeW_wrC_xadd (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
    {i : Int64} {z : Nat} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAtB cells l k [(xaddDir b i r, z)] = true) (he : lab l + Int64.ofNat k = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := fun s c hA =>
  let ⟨σ, hJ, hF, hw⟩ := (Spike.Lib.X64.AllocG.nodeW_wr_xadd hI hb he hp ha s c hA).1
  ⟨noWrC_of_only hw (hoff σ c s.st.1 hJ hF), fun _ h => h⟩

/-- **An `xchgq %r, k(%b)`** of a word unmapped in private memory (`ha`),
off the arena and not the counter word (`hoff`), has `NoWrC`: it writes
only the word at the abstract state's address. -/
theorem nodeW_wrC_xchg (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
    {i : Int64} {z : Nat} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAtB cells l k [(xchgDir b i r, z)] = true) (he : lab l + Int64.ofNat k = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  rw [hp] at hpc
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  have hex := exec_xchg hc ha' (ha σ c s.st.1 hJ hF)
  rw [access_agrees (Spike.Lib.X64.agrees_of_decls hdc _ _)] at hex
  exact ⟨noWrC_of_only (fun L hL => wrAt_rmw hex hL) (hoff σ c s.st.1 hJ hF), fun _ h => h⟩

/-! ## Inside `Wf` -/

/-- **A store's states inside `Wf`** at the frames `fs`: `movq %r, i(%b)`
(`hb`) of a word unmapped in private memory (`ha`), off the arena and not
the counter word (`hoff`), its states with the state's facts (`hst`, moved
by `K`), its pc off the take and abort sites (`htk`, `habt`), its next pc
off both abort phases' pcs (`hph`), the control at the node's invariant
(`hJ`), the frames placed (`hpl`). -/
theorem nodeW_wfSt (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
    {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(stDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hstep := st_step (R := R) hI hb he ha
  have hwr := nodeW_wrC_st (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (fs := fs) (R := R)
    hI hb he rfl ha hoff
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    hwr (nodeW_abortWf_off habt)

/-- **A `lock xaddq`'s states inside `Wf`** at the frames `fs` (as
`nodeW_wfSt`): `lock xaddq %r, i(%b)` (`hb`) of a word unmapped in private
memory (`ha`), off the arena and not the counter word (`hoff`). -/
theorem nodeW_wfXadd (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
    {i : Int64} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(xaddDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hstep := xadd_step (R := R) hI hb he ha
  have hwr := nodeW_wrC_xadd (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (fs := fs) (R := R)
    hI hb he rfl ha hoff
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    hwr (nodeW_abortWf_off habt)

/-- **An `xchgq`'s states inside `Wf`** at the frames `fs` (as
`nodeW_wfSt`): `xchgq %r, i(%b)` (`hb`) of a word unmapped in private
memory (`ha`), off the arena and not the counter word (`hoff`). -/
theorem nodeW_wfXchg (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
    {i : Int64} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(xchgDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hstep := xchg_step (R := R) hI hb he ha
  have hwr := nodeW_wrC_xchg (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (fs := fs) (R := R)
    hI hb he rfl ha hoff
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    hwr (nodeW_abortWf_off habt)

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.st_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.st_step

/-- info: 'Spike.Lib.X64.WakeWf.xadd_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.xadd_step

/-- info: 'Spike.Lib.X64.WakeWf.xchg_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.xchg_step

/-- info: 'Spike.Lib.X64.WakeWf.noWrC_of_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.noWrC_of_only

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wrC_xadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wrC_xadd

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wrC_xchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wrC_xchg

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wfSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wfSt

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wfXadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wfXadd

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wfXchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wfXchg
