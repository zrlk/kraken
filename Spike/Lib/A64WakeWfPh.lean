/-
**wake.w's two abort phases kept off their pcs** (`Wf`'s `AbSt`/`AcSt`,
AArch64): the write abort's phase `WriteAb.Ab lab` and the threads abort's
`ThreadsAb.Ac lab pfx` kept at a block or single instruction none of whose
next pcs is a pc of either phase, from one check per block, decided at the
program's code labels (`labC lo wakeProg`) and moved to any labels agreeing
with them where they resolve (`hlab`, no absolute address).

- `acLabs`, `acPcs_congr`, `blkAcC`, `blkAcC_congr`: the labels `acPcs`
  reads, and `ThreadsAcSt.blkAc` reading the block's and those only.
- `phOff`, `siOff`, `phOff_congr`, `siOff_congr`: the check of a block
  (`blkAbC ∧ blkAc`) and of a single instruction (its next pc off both
  phases' pcs).
- `phOffW`, `siOffW`, `phOffW_sound`, `siOffW_sound`: the checks at the
  code labels with every label read resolving, to any `L.lab` agreeing.
- `blkW_phSt`: a covered block's states in `AbSt ∧ AcSt` from `phOff`.
- `nodeW_phSt`: a single instruction's (a cell other than an `svc`, its
  leaves 4 bytes on, `nodeW_wcG`'s `hstep`) from `siOff`.
-/
import Spike.Lib.A64WakeWfN
import Spike.Lib.A64AllocGAb
import Spike.Lib.A64ThreadsAcSt
import Spike.Lib.A64WakeChild
import Spike.Lib.A64WakePh
import Spike.Lib.A64RelWS

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.LowerA64 (blkLabs aiLab aiTgts_congr labC)
open Spike.Lib.A64.AllocG (blkAbC abLabs abPcs_congr blkAbC_congr)
open Scc.Cert.Link.A64 (codeOf)
open Kraken.Promising.Lower.A64 (CellAt)

/-! ## The threads abort's labels -/

/-- **The labels `acPcs lab pfx` reads**: the spawn's, the dispatcher's and
the threads stub's. -/
def acLabs (pfx : String) : List String :=
  [pfx ++ ".sp6", pfx ++ ".clone9", pfx ++ ".1_spawnfail5", "scc_rt_abort", ".L12_scc_rt_abort.0_entry",
    ".L12_scc_rt_abort.2_next1", ".L12_scc_rt_abort.4_next3", ".L12_scc_rt_abort.6_next5",
    ".L12_scc_rt_abort.8_next7", ".L12_scc_rt_abort.9_is8", Spike.Lib.A64.Abort.threads.fn,
    Spike.Lib.A64.Abort.threads.entry, Spike.Lib.A64.Abort.threads.exit]

/-- **`acPcs` reads the labels of `acLabs` only.** -/
theorem acPcs_congr {lab lab' : Label → Int64} {pfx : String} (h : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    Spike.Lib.A64.ThreadsAb.acPcs lab pfx = Spike.Lib.A64.ThreadsAb.acPcs lab' pfx := by
  simp only [Spike.Lib.A64.ThreadsAb.acPcs, Spike.Lib.A64.ThreadsAb.pcRet,
    Spike.Lib.A64.ThreadsAb.cloneAt, Spike.Lib.A64.ThreadsAb.pcSt, Spike.Lib.A64.ThreadsAb.tailPcs,
    Spike.Lib.A64.ThreadsAb.failPcs, Spike.Lib.A64.WriteAb.dispEPcs, Spike.Lib.A64.ThreadsAb.dispTPcs,
    Spike.Lib.A64.ThreadsAb.g5Pcs, Spike.Lib.A64.ThreadsAb.stubPcs]
  rw [h _ (by simp [acLabs] : pfx ++ ".sp6" ∈ acLabs pfx), h _ (by simp [acLabs] : pfx ++ ".clone9" ∈ acLabs pfx),
    h _ (by simp [acLabs] : pfx ++ ".1_spawnfail5" ∈ acLabs pfx),
    h "scc_rt_abort" (by simp [acLabs]), h ".L12_scc_rt_abort.0_entry" (by simp [acLabs]),
    h ".L12_scc_rt_abort.2_next1" (by simp [acLabs]), h ".L12_scc_rt_abort.4_next3" (by simp [acLabs]),
    h ".L12_scc_rt_abort.6_next5" (by simp [acLabs]), h ".L12_scc_rt_abort.8_next7" (by simp [acLabs]),
    h ".L12_scc_rt_abort.9_is8" (by simp [acLabs]), h Spike.Lib.A64.Abort.threads.fn (by simp [acLabs]),
    h Spike.Lib.A64.Abort.threads.entry (by simp [acLabs]), h Spike.Lib.A64.Abort.threads.exit (by simp [acLabs])]

/-- `ThreadsAcSt.blkAc` (the same definition). -/
abbrev blkAcC (lab : Label → Int64) (pfx : String) (pc ra : Int64) (blk : List Directive) : Bool :=
  blkAc lab pfx pc ra blk

/-- **`blkAc` reads the labels at the block's targets and `acLabs` only.** -/
theorem blkAcC_congr {lab lab' : Label → Int64} {pfx : String} {pc ra : Int64} {blk : List Directive}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    blkAcC lab pfx pc ra blk = blkAcC lab' pfx pc ra blk := by
  unfold blkAcC blkAc
  rw [acPcs_congr ha]
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

/-- **A block's targets off both phases' pcs**, the block at `lab l + 4 k`,
its `ret`s to `lab rl`. -/
def phOff (lab : Label → Int64) (pfx : String) (l : Label) (k : Nat) (rl : Label) (blk : List Directive) : Bool :=
  blkAbC lab (lab l + Int64.ofNat (4 * k)) (lab rl) blk && blkAcC lab pfx (lab l + Int64.ofNat (4 * k)) (lab rl) blk

/-- **A single instruction's next pc off both phases' pcs**, at `lab l + 4 k`. -/
def siOff (lab : Label → Int64) (pfx : String) (l : Label) (k : Nat) : Bool :=
  !(Spike.Lib.A64.WriteAb.abPcs lab).contains (lab l + Int64.ofNat (4 * k) + 4) &&
    !(Spike.Lib.A64.ThreadsAb.acPcs lab pfx).contains (lab l + Int64.ofNat (4 * k) + 4)

/-- The labels `phOff` reads. -/
def phLabs (pfx : String) (l rl : Label) (blk : List Directive) : List String :=
  l :: rl :: blkLabs blk ++ abLabs ++ acLabs pfx

theorem phOff_congr {lab lab' : Label → Int64} {pfx : String} {l rl : Label} {k : Nat} {blk : List Directive}
    (h : ∀ x ∈ phLabs pfx l rl blk, lab x = lab' x) : phOff lab pfx l k rl blk = phOff lab' pfx l k rl blk := by
  unfold phOff
  have hb : ∀ x ∈ blkLabs blk, lab x = lab' x := fun x hx => h x (by simp [phLabs, hx])
  have ha : ∀ x ∈ abLabs, lab x = lab' x := fun x hx => h x (by simp [phLabs, hx])
  have hc : ∀ x ∈ acLabs pfx, lab x = lab' x := fun x hx => h x (by simp [phLabs, hx])
  rw [blkAbC_congr hb ha, blkAcC_congr hb hc, h l (by simp [phLabs]), h rl (by simp [phLabs])]

theorem siOff_congr {lab lab' : Label → Int64} {pfx : String} {l : Label} {k : Nat}
    (h : ∀ x ∈ phLabs pfx l l [], lab x = lab' x) : siOff lab pfx l k = siOff lab' pfx l k := by
  unfold siOff
  rw [abPcs_congr fun x hx => h x (by simp [phLabs, hx]), acPcs_congr fun x hx => h x (by simp [phLabs, hx]),
    h l (by simp [phLabs])]

/-- **`phOff` at wake's code labels**, every label it reads resolving. -/
def phOffW (pfx : String) (l : Label) (k : Nat) (rl : Label) (blk : List Directive) : Bool :=
  (phLabs pfx l rl blk).all (fun x => (codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x).isSome) &&
    phOff (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg) pfx l k rl blk

/-- **`siOff` at wake's code labels**, every label it reads resolving. -/
def siOffW (pfx : String) (l : Label) (k : Nat) : Bool :=
  (phLabs pfx l l []).all (fun x => (codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x).isSome) &&
    siOff (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg) pfx l k

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- `lab` is the code labels at every resolving label of `xs`. -/
theorem lab_labC {xs : List String}
    (h : xs.all (fun x => (codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x).isSome) = true) :
    ∀ x ∈ xs, lab x = labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x := fun x hx => by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h x hx)
  rw [hlab x y hy]; simp [labC, hy]

/-- **`phOffW` at any labels agreeing with the code labels.** -/
theorem phOffW_sound {pfx : String} {l rl : Label} {k : Nat} {blk : List Directive}
    (h : phOffW pfx l k rl blk = true) : phOff lab pfx l k rl blk = true := by
  simp only [phOffW, Bool.and_eq_true] at h
  rw [phOff_congr (lab_labC hlab h.1)]; exact h.2

/-- **`siOffW` at any labels agreeing with the code labels.** -/
theorem siOffW_sound {pfx : String} {l : Label} {k : Nat} (h : siOffW pfx l k = true) :
    siOff lab pfx l k = true := by
  simp only [siOffW, Bool.and_eq_true] at h
  rw [siOff_congr (lab_labC hlab h.1)]; exact h.2

end Sound

/-! ## The phases kept at the nodes -/

section Nodes

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {pfx : String}

/-- **A covered block's states keep both phases** (`blkW_abSt`,
`blkW_acStN`), its pcs off the marks' sites (`hpc`), its targets off both
phases' pcs (`h`), every `ret` to `lab rl` (`hret`). -/
theorem blkW_phSt {n : ND} {blk : List Directive} {lo hi : Int} {l rl : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : phOff (_root_.Executable.labels exe).label pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take j)
        ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = (_root_.Executable.labels exe).label rl) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  simp only [phOff, Bool.and_eq_true, he] at h
  exact BlkW.and (blkW_abSt hcode hok hR hal hlo hhi hpc (blkAb_sound h.1 hret))
    (blkW_acStN hcode hok hR hal hlo hhi hpc (blkAc_sound h.2 hret))

/-- **A single instruction's states keep both phases**: a cell other than
an `svc` whose leaves are 4 bytes on (`hstep`), off the take site (`htk`),
its next pc off both phases' pcs (`h`). -/
theorem nodeW_phSt {n : ND} {l : Label} {k : Nat}
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : siOff (_root_.Executable.labels exe).label pfx l k = true)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, -, -, hpc, -⟩ := id hA
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hA
  simp only [siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hsys : abi.atSys s = false := atSvc_false_of_cellAt hc hd
  have htk' : ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha => by
    unfold pcOf; rw [hpc]; exact htk a ha
  have hlab : (_root_.Executable.labels s.exe).label = (_root_.Executable.labels exe).label := by rw [hs]
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.A64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h.1)
  have hnac : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s' :=
    fun s' hs' => Spike.Lib.A64.ThreadsAb.not_ac_of_pc (by rw [hl s' hs', hpc]; exact h.2)
  refine ⟨⟨AbSt.ofLeaves htk' hsys fun t ht => ?_, AcSt.ofLeaves htk' hsys fun _ t ht => ?_⟩, fun _ h => h⟩
  · rw [hex] at ht; cases ht; exact allInv_of_leaf tree hnab
  · rw [hex] at ht; cases ht; exact allInv_of_leaf tree hnac

end Nodes

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.acPcs_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.acPcs_congr

/-- info: 'Spike.Lib.A64.WakeWf.phOffW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.phOffW_sound

/-- info: 'Spike.Lib.A64.WakeWf.blkW_phSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.blkW_phSt

/-- info: 'Spike.Lib.A64.WakeWf.nodeW_phSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.nodeW_phSt
