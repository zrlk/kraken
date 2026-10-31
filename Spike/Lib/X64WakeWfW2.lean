/-
**wake.w's load and take-site nodes inside `Wf`** (x86-64; twin of
`Spike/Lib/A64WakeWfW2.lean`): the per-node obligation of `Wf`
(`Spike/Lib/X64WakeWf.lean`) at a load `movq i(%b), %r` of a word unmapped
in private memory (`scc_rt_stack_free_n`'s), and at the take site's `nop`,
as `WakeWf.nodeW_wfSt` (`Spike/Lib/X64WakeWfW.lean`). Generic in the
layout, the marks, the owned words, the arena and the clone path.

- `ld_step`: the load's one step to `pc + z`, not a `syscall`
  (`nodeW_phSt`'s `hstep`).
- `nodeW_wfLd`: the load's states inside `Wf` at the frames `fs`.
- `site_wf`: the take site's states inside `Wf` (the take lands past the
  `nop` too; a `nop` writes nothing).

**Unlike AArch64**: AArch64's swap (`swp_step`, `nodeW_wfSwp`) is x86-64's
`xchgq` (`WakeWf.xchg_step` / `nodeW_wfXchg`, `Spike/Lib/X64WakeWfW.lean`)
and its release store (`stlr_step`, `nodeW_wfStlr`) a plain `movq`
(`WakeWf.st_step` / `nodeW_wfSt`), so only the load and the site are here;
the load is `ldDir b i r` at `bAddr σ.regs b i` (A64's `ldrDir t b i` at
`rAddr`), of size `z` at byte offset `k` (`blockAtB`); the site's `nop` is
`op64 (.nop 1)` of size `z` (A64's `NOP`, 4 bytes).
-/
import Spike.Lib.X64WakeWfW

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW ND At ldDir bAddr mB eaddr_mB)
open Spike.Lib.X64.Rt (InstOk cellOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt eaddr op64 exec_load_agrees exec_nop)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ' : Marks} {own' : Own} {Tk : State → Prop}
  {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A load of an unmapped word steps to `pc + z`**, its cell not a
`syscall`. -/
theorem ld_step (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
    {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(ldDir b i r, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧ (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b i) = bAddr σ.regs b i := (eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  refine ⟨_, _, hc, fun w w' h => (by cases h),
    exec_load_agrees hc ha' (ha σ c s.st.1 hJ hF) (Spike.Lib.X64.agrees_of_decls hdc _ _), fun s' hu => ?_⟩
  simp only [TreeLeaf] at hu
  obtain ⟨_, rfl⟩ := hu; rfl

/-- **A load's states inside `Wf`** at the frames `fs` (as `nodeW_wfSt`):
`movq i(%b), %r` (`hb`) of a word unmapped in private memory (`ha`); a load
writes nothing. -/
theorem nodeW_wfLd (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64} {i : Int64}
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
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx
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
theorem site_wf (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {l : Label} {k z : Nat}
    (hb : blockAtB cells l k [(op64 (.nop 1), z)] = true) (he : lab l + Int64.ofNat k = n.pc)
    (hst : ∀ s c, At exe endPc R F n s c → SFactsSt2 Λ μ own s Dt)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : ∀ s c, At exe endPc R F n s c → PlacedSE Λ lbl s c fs) :
    ∀ s c, At exe endPc R F n s c → Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac lab pfx) Ctx lbl lsize s c fs := by
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
  have hac : ∀ m, ¬ Spike.Lib.X64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx
      (Kraken.Promising.Lower.X64.after s z m) := fun _ =>
    Spike.Lib.X64.ThreadsAb.not_ac_of_pc (by show s.st.2 + Int64.ofNat z ∉ _; rw [hpc]; exact hph.2)
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

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.ld_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.ld_step

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_wfLd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_wfLd

/-- info: 'Spike.Lib.X64.WakeWf.site_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.site_wf
