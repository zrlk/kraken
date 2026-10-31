/-
**wake.w's quiet nodes inside `Wf`** (x86-64; twin of
`Spike/Lib/A64WakeWfG.lean`): the per-node obligation of `Wf`
(`Spike/Lib/X64WakeWf.lean`) at a covered block or a single instruction
without an event that is off the marks' sites, writes no memory, and whose
targets are off both abort phases' pcs, from the state's facts
(`SFactsSt2`, moved by `K`), one decided phase check (`phOff`/`siOff`,
`Spike/Lib/X64WakeWfPh.lean`), the control's facts at the node's invariant
and the frames placed. Generic in the layout, the marks, the owned words,
the arena and the clone path.

- `blkW_ofJ`, `nodeW_ofJ`: a predicate of the control alone from the node's
  invariant (a block's states keep the node's control).
- `blkW_abortWf`: `AbortWf` at a block whose pcs are off the marks' sites
  (`PcOff`).
- `silentLeaf`: a silent tree's leaves satisfy its predicate.
- `si_step`, `fi_step`: a single instruction without an event (`SI`, or
  `FI` with undefined flags) steps to `pc + z` (`nodeW_phSt`'s `hstep`).
- `blkW_wfQ`, `nodeW_wfQ`, `nodeW_wfQF`: a quiet block's or single
  instruction's states inside `Wf` at the frames `fs`.
- `blkW_w0`, `nodeW_w0`: a node inside `Wf` at the frames `[]` or `[frM]`
  is inside `W0` given the per-state facts `X0` at its states.

**Unlike AArch64**: a block sits at a byte offset `off` of a label
(`blockAtB cells l off`, `lab l + off`), its instructions at
`cellOff blk j`, a single instruction of size `z` (`siOff … z`); no `hal`;
a `ret`'s target is the stack slot at `%rsp` (`hret`, as `blkW_abSt`'s).
Added (no AArch64 twin): `fi_step` and `nodeW_wfQF`, the single
instruction with undefined flags (`FI`, x86-64's flag-setting ALU ops).
-/
import Spike.Lib.X64WakeWfPh

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS Frag Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun SI FI)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {K : State → State → Prop}
  {fs : List TermRun.Frame}

/-! ## The control's facts from the node's invariant -/

/-- **A block's states keep the node's control**: a predicate of the
control holding at the node's invariant holds at every state. -/
theorem blkW_ofJ {Q : Ctl → Prop} {n : ND} {blk : List (Directive × Nat)} (h : ∀ σ c, n.J σ c → Q c) :
    BlkW (fun _ c => Q c) (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ, fun _ h => h⟩

/-- **A node's states have the node's control.** -/
theorem nodeW_ofJ {Q : Ctl → Prop} {n : ND} (h : ∀ σ c, n.J σ c → Q c) :
    NodeW (fun _ c => Q c) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨h σ c hJ, fun _ h => h⟩

/-! ## The abort sites -/

/-- **`AbortWf` at a block whose pcs are off the marks' sites.** -/
theorem blkW_abortWf {Ab Ac : State → Prop} {n : ND} {blk : List (Directive × Nat)}
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk j) → PcOff μ s) :
    BlkW (fun s c => AbortWf ar μ Ab Ac s c fs) (fun _ _ => False) exe endPc R F n blk :=
  fun s _ _ he hn _ _ _ _ _ k hk m _ _ =>
    ⟨abortWf_of_off (hpc k hk { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } he hn rfl).noAbort,
      fun _ h => h⟩

/-! ## A single instruction's step -/

/-- A silent tree's leaves satisfy its predicate. -/
theorem silentLeaf {σ : Type} {P : σ → Prop} :
    ∀ {t : EvTree σ} {x : σ}, Kraken.Promising.Lower.SilentTree P t → TreeLeaf t x → P x
  | .done _, _, h, hl => hl ▸ h
  | .choose _ _, _, h, ⟨i, hl⟩ => silentLeaf (h.2 i) hl
  | .fault .., _, h, _ => h.elim
  | .load .., _, h, _ => h.elim
  | .store .., _, h, _ => h.elim
  | .rmw .., _, h, _ => h.elim
  | .fence .., _, h, _ => h.elim

variable [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {lab : Label → Int64}
  {μ' : Marks} {own' : Own} {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat}

/-- **A single instruction without an event steps to `pc + z`**, its cell
not a `syscall` (`nodeW_phSt`'s `hstep`). -/
theorem si_step (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {si : SI} {z : Nat}
    {l : Label} {k : Nat} (hb : blockAtB cells l k [(si.toDir, z)] = true) (he : lab l + Int64.ofNat k = n.pc) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧ (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hc : CellAt s si.toDir z := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨_, _, hc, fun w w' h => ?_, Spike.Lib.X64.exec_si hc, fun s' hu => ?_⟩
  · cases si; cases h
  · simp only [TreeLeaf] at hu
    subst hu; rfl

/-- **A single instruction with undefined flags steps to `pc + z`**, its
cell not a `syscall` (`nodeW_phSt`'s `hstep`). -/
theorem fi_step (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {fi : FI} {z : Nat}
    {l : Label} {k : Nat} (hb : blockAtB cells l k [(fi.toDir, z)] = true) (he : lab l + Int64.ofNat k = n.pc) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧ (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hc : CellAt s fi.toDir z := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
  refine ⟨_, _, hc, fun w w' h => ?_, hex, fun s' hu => ?_⟩
  · cases fi <;> cases h
  · obtain ⟨_, rfl⟩ := silentLeaf hst hu; rfl

/-! ## Quiet blocks and instructions inside `Wf` -/

/-- **A quiet block's states inside `Wf`** at the frames `fs`: a covered
block (`hb`, `hok`, in the region `R`) whose states have the state's facts
(`hst`, moved by `K`) and pcs off the marks' sites (`hpc`), its targets off
both abort phases' pcs (`hph`, every `ret` to `lab rl`, `hret`), the
control at the node's invariant not `main`'s `ret` at no frame and its runs
well formed (`hJ`), the frames placed (`hpl`). Its instructions are silent
(`AllocG.blkW_noWr`), so it writes no memory. -/
theorem blkW_wfQ (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {l rl : Label} {k : Nat} (hb : blockAtB cells l k blk = true)
    (he : lab l + Int64.ofNat k = n.pc) (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk j) → PcOff μ s)
    (hph : phOff lab pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = lab rl)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  have hnw := Spike.Lib.X64.AllocG.blkW_noWr (F := F) hI hb he hok hR hlo hhi
  have hl := hI.labOk
  subst hl
  have hP := blkW_phSt (Cl := Cl) (F := F) hcode hok hR hlo hhi hpc he hph hret
  refine blkW_wf hst (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.1,
    fun _ h => h⟩) (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.2,
    fun _ h => h⟩) hcl (fun s σ c a b d e f g hJc j hj m hA hD => ⟨⟨(hJ σ c hJc).1,
      (hpl s σ c a b d e f g hJc j hj m hA hD).1, (hJ σ c hJc).2⟩, fun _ h => h⟩)
    (blkW_noWrC hnw) (blkW_abortWf hpc)

/-- **A quiet single instruction's states inside `Wf`** at the frames `fs`:
an instruction without an event (`hb`) whose states have the state's facts
(`hst`, moved by `K`), its pc off the take and abort sites (`htk`,
`habt`), its next pc off
both abort phases' pcs (`hph`), the control at the node's invariant (`hJ`),
the frames placed (`hpl`). -/
theorem nodeW_wfQ (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND}
    {si : SI} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hstep := si_step (R := R) (F := F) hI hb he
  have hnw := Spike.Lib.X64.AllocG.nodeW_noWr_si (R := R) (F := F) hI hb he rfl
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_noWrC hnw) (nodeW_abortWf_off habt)

/-- **A quiet single instruction with undefined flags inside `Wf`** (as
`nodeW_wfQ`, at an `FI`). -/
theorem nodeW_wfQF (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND}
    {fi : FI} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hstep := fi_step (R := R) (F := F) hI hb he
  have hnw := Spike.Lib.X64.AllocG.nodeW_noWr_fi (R := R) (F := F) hI hb he rfl
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_noWrC hnw) (nodeW_abortWf_off habt)

/-! ## Inside `W0` -/

omit [Kraken.Executable.ValidLayout exe] in
/-- **A block inside `W0`** from one inside `Wf` at the frames `[]` or
`[frM]` (`hfs`) and the per-state facts `X0` at its states (`hx`). -/
theorem blkW_w0 {Ab Ac : State → Prop} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {n : ND}
    {blk : List (Directive × Nat)} (hfs : fs = [] ∨ fs = [frM])
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

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.blkW_ofJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_ofJ

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_ofJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_ofJ

/-- info: 'Spike.Lib.X64.WakeWf.blkW_abortWf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_abortWf

/-- info: 'Spike.Lib.X64.WakeWf.silentLeaf' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.silentLeaf

/-- info: 'Spike.Lib.X64.WakeWf.si_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.si_step

/-- info: 'Spike.Lib.X64.WakeWf.fi_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.fi_step

/-- info: 'Spike.Lib.X64.WakeWf.blkW_wfQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_wfQ

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wfQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wfQ

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wfQF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wfQF

/-- info: 'Spike.Lib.X64.WakeWf.blkW_w0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_w0

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_w0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_w0
