/-
**hello.w's writing, lock and take nodes inside `Wf` at its threads abort
phase** (AArch64, the `hti` chain): the twins of
`A64WakeWfW.nodeW_wfSt` / `nodeW_wfLdop` and `A64WakeWfW2.nodeW_wfSwp` /
`nodeW_wfLdr` / `nodeW_wfStlr` / `site_wf` at hello.w's threads abort phase
`HelloWf.AcH` (`HelloWf.siOffH`, `HelloWf.nodeW_phStH`) instead of wake's
`ThreadsAb.Ac`. The steps (`st_step`, `ldop_step`, `swp_step`, `ldr_step`,
`stlr_step`), the writes (`nodeW_wrC_st`, `nodeW_wrC_ldop`, `wrAt_rmw`,
`wrAt_store`, `noWr_load`) and `WakeWf.nodeW_wf` are generic and reused.

- `nodeW_wfStH`, `nodeW_wfLdopH`: the store's and the RMW's states.
- `nodeW_wfSwpH`, `nodeW_wfLdrH`, `nodeW_wfStlrH`: the swap's, the load's and
  the release store's states.
- `site_wfH`: the take site's states.
-/
import Spike.Lib.A64HelloWfPh
import Spike.Lib.A64WakeWfW2

namespace Spike.Lib.A64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW ND At strDir ldopDir ldrDir rAddr)
open Spike.Lib.A64.Rt (InstOk cellOf)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt exec_swp exec_ldr_agrees exec_stlr_agrees exec_nop)
open Spike.Lib.A64.WakeWf (Wf RunWf nodeW_wf nodeW_noWrC nodeW_abortWf_off nodeW_ofJ nodeW_wrC_st nodeW_wrC_ldop
  st_step ldop_step swp_step ldr_step stlr_step swpDir stlrDir NoWrC noWrC_of_only noWrC_of_noWr
  abortWf_of_off)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  {prog : List Directive} {lab : Label → Int64} {μ' : Marks} {own' : Own} {Tk : State → Prop}
  {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store's states inside `Wf` at `AcH`** (`WakeWf.nodeW_wfSt` at hello's
threads abort phase): `str Xt, [Xn, #i]` of a word unmapped in private memory
(`ha`), off the arena and not the counter word (`hoff`). -/
theorem nodeW_wfStH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} (hb : blockAt prog l k [strDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (rAddr σ.regs b i).toNat ∧ (rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phStH (Cl := Cl) (R := R) (F := F) he hph htk (st_step hI hb he ha)
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_wrC_st hI hb he rfl ha hoff) (nodeW_abortWf_off habt)

/-- **An RMW's states inside `Wf` at `AcH`** (as `nodeW_wfStH`):
`ld<op> Xs, Xt, [Xn]` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeW_wfLdopH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {op : AtomicOp}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt prog l k [ldopDir op kk rs rt b] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phStH (Cl := Cl) (R := R) (F := F) he hph htk (ldop_step hI hb he ha)
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_wrC_ldop hI hb he rfl ha hoff) (nodeW_abortWf_off habt)

/-- **A swap's states inside `Wf` at `AcH`** (as `nodeW_wfLdopH`):
`swp<k> Xs, Xt, [Xn]` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeW_wfSwpH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {kk : Kraken.RmwKind}
    {rs rt b : XReg} {l : Label} {k : Nat} (hb : blockAt prog l k [swpDir kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phStH (Cl := Cl) (R := R) (F := F) he hph htk (swp_step hI hb he ha)
  have hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := by
    rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJc⟩
    have hc := cellOf hI hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
    have hex := exec_swp hc (by rw [ha']; exact ha σ c s.st.1 hJc hD)
    rw [hdc, ha'] at hex
    exact ⟨noWrC_of_only (fun L hL => wrAt_rmw hex hL) (hoff σ c hJc), fun _ h => h⟩
  exact nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    hwr (nodeW_abortWf_off habt)

/-- **A load's states inside `Wf` at `AcH`** (as `nodeW_wfStH`):
`ldr Xt, [Xn, #i]` of a word unmapped in private memory (`ha`); a load
writes nothing. -/
theorem nodeW_wfLdrH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} (hb : blockAt prog l k [ldrDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phStH (Cl := Cl) (R := R) (F := F) he hph htk (ldr_step hI hb he ha)
  have hwr : NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
    rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJc⟩
    have hc := cellOf hI hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
    exact ⟨noWr_load (exec_ldr_agrees hc ha' (ha σ c s.st.1 hJc hD) (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)),
      fun _ h => h⟩
  exact nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_noWrC hwr) (nodeW_abortWf_off habt)

/-- **A release store's states inside `Wf` at `AcH`** (as `nodeW_wfLdopH`):
`stlr Xt, [Xn]` of a word unmapped in private memory (`ha`), off the arena
and not the counter word (`hoff`). -/
theorem nodeW_wfStlrH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t b : XReg}
    {l : Label} {k : Nat} (hb : blockAt prog l k [stlrDir t b] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phStH (Cl := Cl) (R := R) (F := F) he hph htk (stlr_step hI hb he ha)
  have hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := by
    rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJc⟩
    have hc := cellOf hI hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
    have hex := exec_stlr_agrees hc (by rw [ha']; exact ha σ c s.st.1 hJc hD)
      (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
    rw [ha'] at hex
    exact ⟨noWrC_of_only (fun L hL => wrAt_store hex hL) (hoff σ c hJc), fun _ h => h⟩
  exact nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    hwr (nodeW_abortWf_off habt)

/-- **The take site's states inside `Wf` at `AcH`** (`WakeWf.site_wf` at
hello's threads abort phase): a `nop` whose states have the state's facts
(`hst`), off the abort sites (`habt`), its next pc off both abort phases'
pcs (`hph`; the take lands there too). -/
theorem site_wfH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {l : Label} {k : Nat}
    (hb : blockAt prog l k [.instr ⟨.W64, .NOP⟩] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : ∀ s c, At exe endPc R F n s c → SFactsSt2 Λ μ own s Dt)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : ∀ s c, At exe endPc R F n s c → PlacedSE Λ lbl s c fs) :
    ∀ s c, At exe endPc R F n s c → Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl
      (AcH lab pfx) Ctx lbl lsize s c fs := by
  have hl := hI.labOk
  subst hl
  intro s c hA
  obtain ⟨hs, hn, -, hpc, σ, -, -, hJc⟩ := id hA
  have hc := cellOf hI hb he hs hn hpc
  have hex := exec_nop hc
  have hsys : abi.atSys s = false := atSvc_false_of_cellAt hc (by intro imm h; cases h)
  simp only [siOffH, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hph
  have hab : ∀ m, ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label
      (Kraken.Promising.Lower.A64.after s 4 m) := fun _ =>
    Spike.Lib.A64.WriteAb.not_ab_of_pc (by show s.st.2 + Int64.ofNat 4 ∉ _; rw [hpc]; exact hph.1)
  have hac : ∀ m, ¬ AcH (_root_.Executable.labels exe).label pfx
      (Kraken.Promising.Lower.A64.after s 4 m) := fun _ =>
    Spike.Lib.A64.Hello.ThreadsAb.not_ac_of_pc (by show s.st.2 + Int64.ofNat 4 ∉ _; rw [hpc]; exact hph.2)
  have hsk : ∀ m, abi.skip (abi.setDmem s m) =
      Kraken.Promising.Lower.A64.after (abi.setDmem s m) 4 (abi.setDmem s m).st.1 := fun m =>
    Scc.Sem.A64.abi_skip_of_cellAt (st := abi.setDmem s m) ⟨hc.valid, hc.ne, hc.code⟩
  have hw := noWrC_of_noWr (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (c := c)
    (noWr_done hex) fs
  refine Wf.intro (hst s c hA) ⟨fun _ _ tr ht => ?_, fun _ h => (by rw [hsys] at h; cases h),
      fun _ _ _ _ m => (by rw [hsk]; exact hab _)⟩
    ⟨fun _ _ tr ht => ?_, fun _ h => (by rw [hsys] at h; cases h), fun _ _ _ _ m => (by rw [hsk]; exact hac _)⟩
    hcl (hJ σ c hJc).1 (hpl s c hA) hw.1 hw.2 (hJ σ c hJc).2
    (abortWf_of_off fun k a ha => by unfold pcOf; rw [hpc]; exact habt k a ha)
  · rw [hex] at ht; cases ht; exact hab _
  · rw [hex] at ht; cases ht; exact hac _

end Spike.Lib.A64.HelloWf

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_wfStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_wfStH

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_wfLdopH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_wfLdopH

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_wfSwpH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_wfSwpH

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_wfLdrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_wfLdrH

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_wfStlrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_wfStlrH

/-- info: 'Spike.Lib.A64.HelloWf.site_wfH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.site_wfH
