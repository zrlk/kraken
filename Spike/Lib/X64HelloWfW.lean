/-
**hello.w's writing, load and take-site nodes inside `Wf` at its threads abort phase** (x86-64; the twin of
`Spike/Lib/A64HelloWfW.lean`): `X64WakeWfW.nodeW_wfSt` / `nodeW_wfXadd` / `nodeW_wfXchg` and
`X64WakeWfW2.nodeW_wfLd` / `site_wf` at hello.w's threads abort phase `Hello.ThreadsAb.AcH` (`HelloWf.siOff`,
`HelloWf.nodeW_phSt`) instead of wake's `ThreadsAb.Ac`. The steps (`st_step`, `xadd_step`, `xchg_step`,
`ld_step`), the writes (`nodeW_wrC_st`, `nodeW_wrC_xadd`, `nodeW_wrC_xchg`, `noWr_load`) and `WakeWf.nodeW_wf`
are generic and reused.

- `nodeW_wfStH`, `nodeW_wfXaddH`, `nodeW_wfXchgH`: the store's and the RMWs' states.
- `nodeW_wfLdH`: the load's states.
- `site_wfH`: the take site's states.

Unlike AArch64, the RMWs are `lock xaddq` and `xchgq` (AArch64's one `ld<op>` and `swp`), the release store is a
plain `movq` (`nodeW_wfStH`), and every instruction sits at a byte offset with a size `z` (`siOff … z`).
-/
import Spike.Lib.X64HelloWfPh
import Spike.Lib.X64WakeWfW2

namespace Spike.Lib.X64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW ND At stDir xaddDir xchgDir ldDir bAddr mB eaddr_mB)
open Spike.Lib.X64.Rt (InstOk cellOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt eaddr op64 exec_load_agrees exec_nop)
open Spike.Lib.X64.WakeWf hiding siOff phOff nodeW_phSt blkW_phSt acLabs phLabs phOffW siOffW

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ' : Marks} {own' : Own} {Tk : State → Prop}
  {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store's states inside `Wf`** at the frames `fs`: `movq %r, i(%b)`
(`hb`) of a word unmapped in private memory (`ha`), off the arena and not
the counter word (`hoff`), its states with the state's facts (`hst`, moved
by `K`), its pc off the take and abort sites (`htk`, `habt`), its next pc
off both abort phases' pcs (`hph`), the control at the node's invariant
(`hJ`), the frames placed (`hpl`). -/
theorem nodeW_wfStH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
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
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx
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
`nodeW_wfStH`): `lock xaddq %r, i(%b)` (`hb`) of a word unmapped in private
memory (`ha`), off the arena and not the counter word (`hoff`). -/
theorem nodeW_wfXaddH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
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
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx
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
`nodeW_wfStH`): `xchgq %r, i(%b)` (`hb`) of a word unmapped in private
memory (`ha`), off the arena and not the counter word (`hoff`). -/
theorem nodeW_wfXchgH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
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
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx
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

/-- **A load's states inside `Wf`** at the frames `fs` (as `nodeW_wfStH`):
`movq i(%b), %r` (`hb`) of a word unmapped in private memory (`ha`); a load
writes nothing. -/
theorem nodeW_wfLdH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
    {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(ldDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx
      lbl lsize s c fs) K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk (ld_step hI hb he ha)
  have hwr : NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
    rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJc⟩
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
    exact ⟨noWr_load (exec_load_agrees hc ha' (ha σ c s.st.1 hJc hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)),
      fun _ h => h⟩
  exact nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_noWrC hwr) (nodeW_abortWf_off habt)

/-- **The take site's states inside `Wf`** at the frames `fs`: a `nop`
(`hb`, at the marks' take site or not) whose states have the state's facts
(`hst`), off the abort sites (`habt`), its next pc off both abort phases'
pcs (`hph`; the take lands there too), the control at the node's invariant
(`hJ`), the frames placed (`hpl`). -/
theorem site_wfH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {l : Label} {k z : Nat}
    (hb : blockAtB cells l k [(op64 (.nop 1), z)] = true) (he : lab l + Int64.ofNat k = n.pc)
    (hst : ∀ s c, At exe endPc R F n s c → SFactsSt2 Λ μ own s Dt)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : ∀ s c, At exe endPc R F n s c → PlacedSE Λ lbl s c fs) :
    ∀ s c, At exe endPc R F n s c → Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx lbl lsize s c fs := by
  have hl := hI.labOk
  subst hl
  intro s c hA
  obtain ⟨hs, hn, -, hpc, σ, -, -, hJc⟩ := id hA
  have hc := cellOf hI hb he hs hn hpc
  have hex := exec_nop hc
  have hsys : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  simp only [siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hph
  have hab : ∀ m, ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label
      (Kraken.Promising.Lower.X64.after s z m) := fun _ =>
    Spike.Lib.X64.WriteAb.not_ab_of_pc (by show s.st.2 + Int64.ofNat z ∉ _; rw [hpc]; exact hph.1)
  have hac : ∀ m, ¬ Spike.Lib.X64.Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx
      (Kraken.Promising.Lower.X64.after s z m) := fun _ =>
    Spike.Lib.X64.Hello.ThreadsAb.not_ac_of_pc (by show s.st.2 + Int64.ofNat z ∉ _; rw [hpc]; exact hph.2)
  have hsk : ∀ m, abi.skip (abi.setDmem s m) =
      Kraken.Promising.Lower.X64.after (abi.setDmem s m) z (abi.setDmem s m).st.1 := fun m =>
    Scc.Sem.X64.abi_skip_of_cellAt (st := abi.setDmem s m) ⟨hc.valid, hc.ne, hc.code⟩
  have hw := noWrC_of_noWr (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (c := c)
    (noWr_done hex) fs
  refine Wf.intro (hst s c hA) ⟨fun _ _ tr ht => ?_, fun _ h => (by rw [hsys] at h; cases h),
      fun _ _ _ _ m => (by rw [hsk]; exact hab _)⟩
    ⟨fun _ _ tr ht => ?_, fun _ h => (by rw [hsys] at h; cases h), fun _ _ _ _ m => (by rw [hsk]; exact hac _)⟩
    hcl (hJ σ c hJc).1 (hpl s c hA) hw.1 hw.2 (hJ σ c hJc).2
    (abortWf_of_off fun k a ha => by unfold pcOf; rw [hpc]; exact habt k a ha)
  · rw [hex] at ht; cases ht; exact hab _
  · rw [hex] at ht; cases ht; exact hac _

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.nodeW_wfStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.nodeW_wfStH

/-- info: 'Spike.Lib.X64.HelloWf.nodeW_wfXaddH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.nodeW_wfXaddH

/-- info: 'Spike.Lib.X64.HelloWf.nodeW_wfXchgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.nodeW_wfXchgH

/-- info: 'Spike.Lib.X64.HelloWf.nodeW_wfLdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.nodeW_wfLdH

/-- info: 'Spike.Lib.X64.HelloWf.site_wfH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.site_wfH
