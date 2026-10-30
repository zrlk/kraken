/-
**wake.w's writing nodes inside `Wf`** (AArch64): the per-node obligation
of `Wf` (`Spike/Lib/A64WakeWf.lean`) at a store `str Xt, [Xn, #i]` or an
RMW `ld<op> Xs, Xt, [Xn]` of a word unmapped in private memory, off the
arena and not the counter word (a runtime word: `scc_rt_pinned_next`, a
TCB header), as `WakeWf.nodeW_wfQ` for the quiet ones: the state's facts
(`SFactsSt2`, moved by `K`), one decided phase check (`siOff`), the
control's facts at the node's invariant and the frames placed. Generic in
the layout, the marks, the owned words, the arena and the clone path.

- `st_step`, `ldop_step`: the instruction's one step to `pc + 4`, not an
  `svc` (`nodeW_phSt`'s `hstep`).
- `nodeW_wrC_ldop`: an RMW's `NoWrC` (`nodeW_wrC_st` for the RMW).
- `nodeW_wfSt`, `nodeW_wfLdop`: the store's and the RMW's states inside
  `Wf` at the frames `fs`.
-/
import Spike.Lib.A64WakeWfG

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW ND At strDir ldopDir rAddr)
open Spike.Lib.A64.Rt (InstOk cellOf)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt exec_str_agrees exec_ldop)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  {prog : List Directive} {lab : Label → Int64} {μ' : Marks} {own' : Own} {Tk : State → Prop}
  {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-! ## The steps -/

/-- **A store of an unmapped word steps to `pc + 4`**, its cell not an
`svc`. -/
theorem st_step (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} (hb : blockAt prog l k [strDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧ (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧
      isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  have hc := cellOf hI hb he hs hn hpc
  have ha' : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  refine ⟨_, _, hc, fun imm h => (by simp [strDir] at h),
    exec_str_agrees hc ha' (ha σ c s.st.1 hJ hF) (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _), fun s' hu => ?_⟩
  simp only [TreeLeaf] at hu
  obtain ⟨_, rfl⟩ := hu; rfl

/-- **An RMW of an unmapped word steps to `pc + 4`**, its cell not an
`svc`. -/
theorem ldop_step (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {op : AtomicOp}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt prog l k [ldopDir op kk rs rt b] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧ (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧
      isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  have hc := cellOf hI hb he hs hn hpc
  have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
  refine ⟨_, _, hc, fun imm h => (by simp [ldopDir] at h), exec_ldop hc (by rw [ha']; exact ha σ c s.st.1 hJ hF),
    fun s' hu => ?_⟩
  rw [hdc, EvTree.access_empty] at hu
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

/-- **An RMW** `ld<op> Xs, Xt, [Xn]` of a word unmapped in private memory
(`ha`), off the arena and not the counter word (`hoff`), has `NoWrC`
(`AllocG.nodeW_wr_ldop`). -/
theorem nodeW_wrC_ldop (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {op : AtomicOp}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAt prog l k [ldopDir op kk rs rt b] = true) (he : lab l + Int64.ofNat (4 * k) = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := fun s c hA =>
  let ⟨σ, hJ, hw⟩ := (Spike.Lib.A64.AllocG.nodeW_wr_ldop hI hb he hp ha s c hA).1
  ⟨noWrC_of_only hw (hoff σ c hJ), fun _ h => h⟩

/-! ## Inside `Wf` -/

/-- **A store's states inside `Wf`** at the frames `fs`: `str Xt, [Xn, #i]`
(`hb`) of a word unmapped in private memory (`ha`), off the arena and not
the counter word (`hoff`), its states with the state's facts (`hst`, moved
by `K`), its pc off the take and abort sites (`htk`, `habt`), its next pc
off both abort phases' pcs (`hph`), the control at the node's invariant
(`hJ`), the frames placed (`hpl`). -/
theorem nodeW_wfSt (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} (hb : blockAt prog l k [strDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (rAddr σ.regs b i).toNat ∧ (rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (Spike.Lib.A64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk (st_step hI hb he ha)
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_wrC_st hI hb he rfl ha hoff) (nodeW_abortWf_off habt)

/-- **An RMW's states inside `Wf`** at the frames `fs` (as `nodeW_wfSt`):
`ld<op> Xs, Xt, [Xn]` (`hb`) of a word unmapped in private memory (`ha`),
off the arena and not the counter word (`hoff`). -/
theorem nodeW_wfLdop (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {op : AtomicOp}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt prog l k [ldopDir op kk rs rt b] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (Spike.Lib.A64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk (ldop_step hI hb he ha)
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_wrC_ldop hI hb he rfl ha hoff) (nodeW_abortWf_off habt)

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.nodeW_wfSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.nodeW_wfSt

/-- info: 'Spike.Lib.A64.WakeWf.nodeW_wfLdop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.nodeW_wfLdop
