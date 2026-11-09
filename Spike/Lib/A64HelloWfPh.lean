/-
**hello.w's quiet nodes inside `Wf` at its threads abort phase** (AArch64): the twin of
`Spike/Lib/A64WakeWfPh.lean`'s checks and phase lemmas, and of `A64WakeWfG.blkW_wfQ`/`nodeW_wfQ`, at hello.w's
threads abort phase `Hello.ThreadsAb.AcH` (`.clone13`, the `clone` the `25`th instruction of `.sp6`, the result at
`[sp + 112]`) instead of wake's `ThreadsAb.Ac` (`.clone9`). Everything below them (`blkW_abSt`, `blkW_acStN`,
`AbSt.ofLeaves`, `AcSt.ofLeaves`, `WakeWf.blkW_wf`/`nodeW_wf`, `HelloThreadsAcSt.blkAc_sound`) is generic
and reused.

- `acLabsH`, `acPcsH_congr`: the labels `acPcsH` reads.
- `blkAcH`, `blkAcH_congr`; `phOffH`, `siOffH`: a block's targets / an instruction's next pc off both phases' pcs.
- `phOffHC`, `siOffHC`, `phOffHC_sound`, `siOffHC_sound`: the checks at helloProg's code labels.
- `blkW_phStH`, `nodeW_phStH`: both phases kept at a covered block / a quiet instruction.
- `blkW_wfQH`, `nodeW_wfQH`: a quiet block / instruction inside `Wf … (WriteAb.Ab lab) Cl (AcH lab pfx)`.
-/
import Spike.Lib.A64WakeWfG
import Spike.Lib.A64HelloThreadsAcSt
import Spike.Lib.A64HelloPh

namespace Spike.Lib.A64.HelloWf

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.LowerA64 (blkLabs aiLab aiTgts_congr labC)
open Spike.Lib.A64.AllocG (blkAbC abLabs abPcs_congr blkAbC_congr)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt)
open Spike.Lib.A64.WakeWf (Wf RunWf blkW_wf nodeW_wf blkW_noWrC nodeW_noWrC blkW_abortWf nodeW_abortWf_off nodeW_ofJ
  si_step)

/-- hello.w's threads abort phase at `lab`, `pfx` (`Hello.ThreadsAb.AcH`). -/
abbrev AcH (lab : Label → Int64) (pfx : String) : State → Prop := Spike.Lib.A64.Hello.ThreadsAb.AcH lab pfx

/-- hello.w's pcs of `AcH`. -/
abbrev acPcsH (lab : Label → Int64) (pfx : String) : List Int64 := Spike.Lib.A64.Hello.ThreadsAb.acPcsH lab pfx

/-! ## The threads abort's labels -/

/-- **The labels `acPcsH lab pfx` reads**: the spawn's, the dispatcher's and the threads stub's. -/
def acLabsH (pfx : String) : List String :=
  [pfx ++ ".sp6", pfx ++ ".clone13", pfx ++ ".1_spawnfail5", "scc_rt_abort", ".L12_scc_rt_abort.0_entry",
    ".L12_scc_rt_abort.2_next1", ".L12_scc_rt_abort.4_next3", ".L12_scc_rt_abort.6_next5",
    ".L12_scc_rt_abort.8_next7", ".L12_scc_rt_abort.9_is8", Spike.Lib.A64.Abort.threads.fn,
    Spike.Lib.A64.Abort.threads.entry, Spike.Lib.A64.Abort.threads.exit]

/-- **`acPcsH` reads the labels of `acLabsH` only.** -/
theorem acPcsH_congr {lab lab' : Label → Int64} {pfx : String} (h : ∀ l ∈ acLabsH pfx, lab l = lab' l) :
    acPcsH lab pfx = acPcsH lab' pfx := by
  simp only [acPcsH, Spike.Lib.A64.Hello.ThreadsAb.acPcsH, Spike.Lib.A64.Hello.ThreadsAb.acPcs,
    Spike.Lib.A64.Hello.ThreadsAb.pcRet, Spike.Lib.A64.Hello.ThreadsAb.pcSt,
    Spike.Lib.A64.Hello.ThreadsAb.tailPcs, Spike.Lib.A64.ThreadsAb.failPcs, Spike.Lib.A64.WriteAb.dispEPcs,
    Spike.Lib.A64.ThreadsAb.dispTPcs, Spike.Lib.A64.ThreadsAb.g5Pcs, Spike.Lib.A64.ThreadsAb.stubPcs]
  rw [h _ (by simp [acLabsH] : pfx ++ ".sp6" ∈ acLabsH pfx),
    h _ (by simp [acLabsH] : pfx ++ ".clone13" ∈ acLabsH pfx),
    h _ (by simp [acLabsH] : pfx ++ ".1_spawnfail5" ∈ acLabsH pfx),
    h "scc_rt_abort" (by simp [acLabsH]), h ".L12_scc_rt_abort.0_entry" (by simp [acLabsH]),
    h ".L12_scc_rt_abort.2_next1" (by simp [acLabsH]), h ".L12_scc_rt_abort.4_next3" (by simp [acLabsH]),
    h ".L12_scc_rt_abort.6_next5" (by simp [acLabsH]), h ".L12_scc_rt_abort.8_next7" (by simp [acLabsH]),
    h ".L12_scc_rt_abort.9_is8" (by simp [acLabsH]), h Spike.Lib.A64.Abort.threads.fn (by simp [acLabsH]),
    h Spike.Lib.A64.Abort.threads.entry (by simp [acLabsH]), h Spike.Lib.A64.Abort.threads.exit (by simp [acLabsH])]

/-- hello.w's `blkAc` (`HelloThreadsAcSt.blkAc` at `25 ".clone13"`). -/
abbrev blkAcH (lab : Label → Int64) (pfx : String) (pc ra : Int64) (blk : List Directive) : Bool :=
  Spike.Lib.A64ConsumerA.HelloThreadsAcSt.blkAc lab pfx 25 ".clone13" pc ra blk

/-- **`blkAcH` reads the labels at the block's targets and `acLabsH` only.** -/
theorem blkAcH_congr {lab lab' : Label → Int64} {pfx : String} {pc ra : Int64} {blk : List Directive}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ acLabsH pfx, lab l = lab' l) :
    blkAcH lab pfx pc ra blk = blkAcH lab' pfx pc ra blk := by
  unfold blkAcH Spike.Lib.A64ConsumerA.HelloThreadsAcSt.blkAc
  have e := acPcsH_congr ha
  simp only [acPcsH, Spike.Lib.A64.Hello.ThreadsAb.acPcsH] at e
  rw [e]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc : Spike.Lib.A64.Flow.classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-! ## The checks -/

/-- **A block's targets off both phases' pcs**, the block at `lab l + 4 k`, its `ret`s to `lab rl`. -/
def phOffH (lab : Label → Int64) (pfx : String) (l : Label) (k : Nat) (rl : Label) (blk : List Directive) : Bool :=
  blkAbC lab (lab l + Int64.ofNat (4 * k)) (lab rl) blk && blkAcH lab pfx (lab l + Int64.ofNat (4 * k)) (lab rl) blk

/-- **A single instruction's next pc off both phases' pcs**, at `lab l + 4 k`. -/
def siOffH (lab : Label → Int64) (pfx : String) (l : Label) (k : Nat) : Bool :=
  !(Spike.Lib.A64.WriteAb.abPcs lab).contains (lab l + Int64.ofNat (4 * k) + 4) &&
    !(acPcsH lab pfx).contains (lab l + Int64.ofNat (4 * k) + 4)

/-- The labels `phOffH` reads. -/
def phLabsH (pfx : String) (l rl : Label) (blk : List Directive) : List String :=
  l :: rl :: blkLabs blk ++ abLabs ++ acLabsH pfx

theorem phOffH_congr {lab lab' : Label → Int64} {pfx : String} {l rl : Label} {k : Nat} {blk : List Directive}
    (h : ∀ x ∈ phLabsH pfx l rl blk, lab x = lab' x) : phOffH lab pfx l k rl blk = phOffH lab' pfx l k rl blk := by
  unfold phOffH
  have hb : ∀ x ∈ blkLabs blk, lab x = lab' x := fun x hx => h x (by simp [phLabsH, hx])
  have ha : ∀ x ∈ abLabs, lab x = lab' x := fun x hx => h x (by simp [phLabsH, hx])
  have hc : ∀ x ∈ acLabsH pfx, lab x = lab' x := fun x hx => h x (by simp [phLabsH, hx])
  rw [blkAbC_congr hb ha, blkAcH_congr hb hc, h l (by simp [phLabsH]), h rl (by simp [phLabsH])]

theorem siOffH_congr {lab lab' : Label → Int64} {pfx : String} {l : Label} {k : Nat}
    (h : ∀ x ∈ phLabsH pfx l l [], lab x = lab' x) : siOffH lab pfx l k = siOffH lab' pfx l k := by
  unfold siOffH
  rw [abPcs_congr fun x hx => h x (by simp [phLabsH, hx]), acPcsH_congr fun x hx => h x (by simp [phLabsH, hx]),
    h l (by simp [phLabsH])]

/-- **`phOffH` at helloProg's code labels**, every label it reads resolving. -/
def phOffHC (pfx : String) (l : Label) (k : Nat) (rl : Label) (blk : List Directive) : Bool :=
  (phLabsH pfx l rl blk).all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    phOffH (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg) pfx l k rl blk

/-- **`siOffH` at helloProg's code labels**, every label it reads resolving. -/
def siOffHC (pfx : String) (l : Label) (k : Nat) : Bool :=
  (phLabsH pfx l l []).all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    siOffH (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg) pfx l k

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- `lab` is the code labels at every resolving label of `xs`. -/
theorem lab_labCH {xs : List String}
    (h : xs.all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) = true) :
    ∀ x ∈ xs, lab x = labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg x := fun x hx => by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h x hx)
  rw [hlab x y hy]; simp [labC, hy]

/-- **`phOffHC` at any labels agreeing with the code labels.** -/
theorem phOffHC_sound {pfx : String} {l rl : Label} {k : Nat} {blk : List Directive}
    (h : phOffHC pfx l k rl blk = true) : phOffH lab pfx l k rl blk = true := by
  simp only [phOffHC, Bool.and_eq_true] at h
  rw [phOffH_congr (lab_labCH hlab h.1)]; exact h.2

/-- **`siOffHC` at any labels agreeing with the code labels.** -/
theorem siOffHC_sound {pfx : String} {l : Label} {k : Nat} (h : siOffHC pfx l k = true) :
    siOffH lab pfx l k = true := by
  simp only [siOffHC, Bool.and_eq_true] at h
  rw [siOffH_congr (lab_labCH hlab h.1)]; exact h.2

end Sound

/-! ## The phases kept at the nodes -/

section Nodes

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {pfx : String}

/-- **A covered block's states keep both phases** (`blkW_abSt`, `blkW_acStN`), its pcs off the marks' sites
(`hpc`), its targets off both phases' pcs (`h`), every `ret` to `lab rl` (`hret`). -/
theorem blkW_phStH {n : ND} {blk : List Directive} {lo hi : Int} {l rl : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : phOffH (_root_.Executable.labels exe).label pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take j)
        ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = (_root_.Executable.labels exe).label rl) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  simp only [phOffH, Bool.and_eq_true, he] at h
  exact Spike.Lib.A64.Flow.BlkW.and (blkW_abSt hcode hok hR hal hlo hhi hpc (blkAb_sound h.1 hret))
    (blkW_acStN hcode hok hR hal hlo hhi hpc
      (Spike.Lib.A64ConsumerA.HelloThreadsAcSt.blkAc_sound (off := 112) h.2 hret))

/-- **A single instruction's states keep both phases**: a cell other than an `svc` whose leaves are 4 bytes on
(`hstep`), off the take site (`htk`), its next pc off both phases' pcs (`h`). -/
theorem nodeW_phStH {n : ND} {l : Label} {k : Nat}
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : siOffH (_root_.Executable.labels exe).label pfx l k = true)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, -, -, hpc, -⟩ := id hA
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hA
  simp only [siOffH, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hsys : abi.atSys s = false := atSvc_false_of_cellAt hc hd
  have htk' : ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha => by
    unfold pcOf; rw [hpc]; exact htk a ha
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.A64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h.1)
  have hnac : ∀ s', TreeLeaf tree s' → ¬ AcH (_root_.Executable.labels exe).label pfx s' :=
    fun s' hs' => Spike.Lib.A64.Hello.ThreadsAb.not_ac_of_pc (by rw [hl s' hs', hpc]; exact h.2)
  refine ⟨⟨AbSt.ofLeaves htk' hsys fun t ht => ?_, AcSt.ofLeaves htk' hsys fun _ t ht => ?_⟩, fun _ h => h⟩
  · rw [hex] at ht; cases ht; exact allInv_of_leaf tree hnab
  · rw [hex] at ht; cases ht; exact allInv_of_leaf tree hnac

end Nodes

/-! ## Quiet blocks and instructions inside `Wf` -/

section Wf

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {K : State → State → Prop}
  {fs : List TermRun.Frame}
  [Kraken.Executable.ValidLayout exe] {prog : List Directive} {lab : Label → Int64} {μ' : Marks}
  {own' : Own} {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A quiet block's states inside `Wf` at `AcH`** (`WakeWf.blkW_wfQ` at hello's threads abort phase). -/
theorem blkW_wfQH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {l rl : Label} {k : Nat} (hb : blockAt prog l k blk = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (hph : phOffH lab pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = lab rl)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n blk := by
  have hl := hI.labOk
  subst hl
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hP := blkW_phStH (Cl := Cl) (F := F) hcode hok hR hal hlo hhi hpc he hph hret
  refine blkW_wf hst (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.1,
    fun _ h => h⟩) (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.2,
    fun _ h => h⟩) hcl (fun s σ c a b d e f g hJc j hj m hA hD => ⟨⟨(hJ σ c hJc).1,
      (hpl s σ c a b d e f g hJc j hj m hA hD).1, (hJ σ c hJc).2⟩, fun _ h => h⟩)
    (blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI hb he hok hR hal hlo hhi)) (blkW_abortWf hpc)

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcross`): as `blkW_wfQH`. -/
theorem blkW_wfQHA (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {l rl m : Label} {k jA : Nat}
    (hb : Scc.Cert.Rt.A64.blockAcross prog l k (blk.take jA) m (blk.drop jA) = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (hph : phOffH lab pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = lab rl)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n blk := by
  have hl := hI.labOk
  subst hl
  have hcode := Spike.Lib.A64.code_field_blockAcross hI.lays hI.endOk hb (List.take_append_drop jA blk)
    (q := n.pc) (by rw [hI.labOk]; exact he)
  have hP := blkW_phStH (Cl := Cl) (F := F) hcode hok hR hal hlo hhi hpc he hph hret
  refine blkW_wf hst (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.1,
    fun _ h => h⟩) (fun s σ c a b d e f g hJc j hj m hA hD => ⟨(hP s σ c a b d e f g hJc j hj m hA hD).1.2,
    fun _ h => h⟩) hcl (fun s σ c a b d e f g hJc j hj m hA hD => ⟨⟨(hJ σ c hJc).1,
      (hpl s σ c a b d e f g hJc j hj m hA hD).1, (hJ σ c hJc).2⟩, fun _ h => h⟩)
    (blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWrA hI hb he hok hR hal hlo hhi)) (blkW_abortWf hpc)

/-- **A quiet single instruction's states inside `Wf` at `AcH`** (`WakeWf.nodeW_wfQ` at hello's threads abort
phase). -/
theorem nodeW_wfQH (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : siOffH lab pfx l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.A64.WriteAb.Ab lab) Cl (AcH lab pfx) Ctx lbl lsize s c fs)
      K exe endPc R F n := by
  have hl := hI.labOk
  subst hl
  have hP := nodeW_phStH (Cl := Cl) (R := R) (F := F) he hph htk (si_step hI hb he)
  refine nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c hA => ⟨⟨((nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1, ((nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (nodeW_noWrC (Spike.Lib.A64.AllocG.nodeW_noWr_si hI hb he rfl))
    (nodeW_abortWf_off habt)

end Wf

end Spike.Lib.A64.HelloWf

/-- info: 'Spike.Lib.A64.HelloWf.phOffHC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.phOffHC_sound
/-- info: 'Spike.Lib.A64.HelloWf.blkW_wfQH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.blkW_wfQH
/-- info: 'Spike.Lib.A64.HelloWf.nodeW_wfQH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_wfQH
