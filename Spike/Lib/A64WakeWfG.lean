/-
**wake.w's quiet nodes inside `Wf`** (AArch64): the per-node obligation
of `Wf` (`Spike/Lib/A64WakeWf.lean`) at a covered block or a single
instruction without an event that is off the marks' sites, writes no
memory, and whose targets are off both abort phases' pcs, from the
state's facts (`SFactsSt2`, moved by `K`), one decided phase check
(`phOff`/`siOff`, `Spike/Lib/A64WakeWfPh.lean`), the control's facts at the
node's invariant and the frames placed. Generic in the layout, the marks,
the owned words, the arena and the clone path.

- `blkW_ofJ`, `nodeW_ofJ`: a predicate of the control alone from the node's
  invariant (a block's states keep the node's control).
- `blkW_abortWf`: `AbortWf` at a block whose pcs are off the marks' sites
  (`PcOff`).
- `si_step`: a single instruction without an event steps to `pc + 4`
  (`nodeW_phSt`'s `hstep`).
- `blkW_wfQ`, `nodeW_wfQ`: a quiet block's or single instruction's states
  inside `Wf` at the frames `fs`.
- `blkW_w0`, `nodeW_w0`: a node inside `Wf` at the frames `[]` or `[frM]`
  is inside `W0` given the per-state facts `X0` at its states.
-/
import Spike.Lib.A64WakeWfPh

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS Frag Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {K : State → State → Prop}
  {fs : List TermRun.Frame}

/-! ## The control's facts from the node's invariant -/

/-- **A block's states keep the node's control**: a predicate of the
control holding at the node's invariant holds at every state. -/
theorem blkW_ofJ {Q : Ctl → Prop} {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → Q c) :
    BlkW (fun _ c => Q c) (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ, fun _ h => h⟩

/-- **A node's states have the node's control.** -/
theorem nodeW_ofJ {Q : Ctl → Prop} {n : ND} (h : ∀ σ c, n.J σ c → Q c) :
    NodeW (fun _ c => Q c) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨h σ c hJ, fun _ h => h⟩

/-! ## The abort sites -/

/-- **`AbortWf` at a block whose pcs are off the marks' sites.** -/
theorem blkW_abortWf {Ab Ac : State → Prop} {n : ND} {blk : List Directive}
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s) :
    BlkW (fun s c => AbortWf ar μ Ab Ac s c fs) (fun _ _ => False) exe endPc R F n blk :=
  fun s _ _ he hn _ _ _ _ _ k hk m _ _ =>
    ⟨abortWf_of_off (hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl).noAbort, fun _ h => h⟩

/-! ## A single instruction's step -/

variable [Kraken.Executable.ValidLayout exe] {prog : List Directive} {lab : Label → Int64} {μ' : Marks}
  {own' : Own} {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A single instruction without an event steps to `pc + 4`**, its cell
not an `svc` (`nodeW_phSt`'s `hstep`). -/
theorem si_step (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {si : Spike.Lib.A64.Flow.SI}
    {l : Label} {k : Nat} (hb : blockAt prog l k [si.toDir] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧ (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧
      isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hc : CellAt s si.toDir 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  refine ⟨_, _, hc, fun imm h => ?_, Spike.Lib.A64.Flow.exec_si hc, fun s' hu => ?_⟩
  · cases si <;> cases h
  · simp only [TreeLeaf] at hu
    subst hu; rfl

/-! ## Quiet blocks and instructions inside `Wf` -/

/-- **A quiet block's states inside `Wf`** at the frames `fs`: a covered
block (`hb`, `hok`, in the region `R`) whose states have the state's facts
(`hst`, moved by `K`) and pcs off the marks' sites (`hpc`), its targets off
both abort phases' pcs (`hph`, every `ret` to `lab rl`, `hret`), the
control at the node's invariant not `main`'s `ret` at no frame and its runs
well formed (`hJ`), the frames placed (`hpl`). Its instructions are silent
(`AllocG.blkW_noWr`), so it writes no memory. -/
theorem blkW_wfQ (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {l rl : Label} {k : Nat} (hb : blockAt prog l k blk = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (hph : phOff lab pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = lab rl)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (Spike.Lib.A64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n blk := by
  have hl := hI.labOk
  subst hl
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hP := blkW_phSt (Cl := Cl) (F := F) hcode hok hR hal hlo hhi hpc he hph hret
  refine blkW_wf hst (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.1,
    fun _ h => h⟩) (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.2,
    fun _ h => h⟩) hcl (fun s σ c a b d e f g hJc j hj m hA hD => ⟨⟨(hJ σ c hJc).1,
      (hpl s σ c a b d e f g hJc j hj m hA hD).1, (hJ σ c hJc).2⟩, fun _ h => h⟩)
    (blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI hb he hok hR hal hlo hhi)) (blkW_abortWf hpc)

/-- **A quiet single instruction's states inside `Wf`** at the frames `fs`:
an instruction without an event (`hb`) whose states have the state's facts
(`hst`, moved by `K`), its pc off the take and abort sites (`htk`,
`habt`), its next pc off
both abort phases' pcs (`hph`), the control at the node's invariant (`hJ`),
the frames placed (`hpl`). -/
theorem nodeW_wfQ (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (Spike.Lib.A64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk
    (si_step hI hb he)
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_noWrC (Spike.Lib.A64.AllocG.nodeW_noWr_si hI hb he rfl))
    (nodeW_abortWf_off habt)

/-! ## Inside `W0` -/

omit [Kraken.Executable.ValidLayout exe] in
/-- **A block inside `W0`** from one inside `Wf` at the frames `[]` or
`[frM]` (`hfs`) and the per-state facts `X0` at its states (`hx`). -/
theorem blkW_w0 {Ab Ac : State → Prop} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {n : ND}
    {blk : List Directive} (hfs : fs = [] ∨ fs = [frM])
    (hx : BlkW (fun s _ => X0 s) (fun _ _ => False) exe endPc R F n blk)
    (hw : BlkW (fun s c => Wf Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 s c fs) K exe endPc R F n blk) :
    BlkW (fun s c => W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs) K exe endPc R F n blk :=
  fun s σ c a b d e f g hJ k hk m hA hD =>
    ⟨⟨hfs, (hx s σ c a b d e f g hJ k hk m hA hD).1, (hw s σ c a b d e f g hJ k hk m hA hD).1⟩,
      (hw s σ c a b d e f g hJ k hk m hA hD).2⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node inside `W0`** (as `blkW_w0`). -/
theorem nodeW_w0 {Ab Ac : State → Prop} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {n : ND}
    (hfs : fs = [] ∨ fs = [frM]) (hx : NodeW (fun s _ => X0 s) (fun _ _ => False) exe endPc R F n)
    (hw : NodeW (fun s c => Wf Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 s c fs) K exe endPc R F n) :
    NodeW (fun s c => W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs) K exe endPc R F n :=
  fun s c hA => ⟨⟨hfs, (hx s c hA).1, (hw s c hA).1⟩, (hw s c hA).2⟩

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.blkW_wfQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.blkW_wfQ

/-- info: 'Spike.Lib.A64.WakeWf.nodeW_wfQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.nodeW_wfQ
