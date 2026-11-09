/-
**wake.w's two abort phases kept off their pcs** (`Wf`'s `AbSt`/`AcSt`,
x86-64; twin of `Spike/Lib/A64WakeWfPh.lean`): the write
abort's phase `WriteAb.Ab lab` and the threads abort's `ThreadsAb.Ac lab pfx`
kept at a block or single instruction none of whose next pcs is a pc of
either phase, from one check per block, decided at the cells' code labels
(`labC lo wakeCells`) and moved to any labels agreeing with them where they
resolve (`hlab`, no absolute address).

- `acLabs`, `acPcs_congr`, `blkAcC`, `blkAcC_congr`: the labels `acPcs`
  reads, and `ThreadsAcSt.blkAc` reading the block's and those only.
- `phOff`, `siOff`, `phOff_congr`, `siOff_congr`: the check of a block
  (`blkAbC ∧ blkAc`) and of a single instruction (its next pc off both
  phases' pcs).
- `phOffW`, `siOffW`, `phOffW_sound`, `siOffW_sound`: the checks at the
  code labels with every label read resolving, to any `L.lab` agreeing.
- `blkW_phSt`: a covered block's states in `AbSt ∧ AcSt` from `phOff`.
- `nodeW_phSt`: a single instruction's (a cell other than a `syscall`, its
  leaves `z` bytes on) from `siOff`.

**Unlike AArch64**: offsets are bytes (`lab l + k`, AArch64's
`lab l + 4 k`) and `siOff` takes the instruction's size `z` (its next pc
`lab l + k + z`, AArch64's `+ 4`); the labels resolve by
`codeLabel lo wakeCells` (AArch64's `codeOf lo wakeProg`); `blkW_phSt` has
no `hal` (x86-64's `blkW_abSt`/`blkW_acStN` have none); `nodeW_phSt`'s
`hstep` is at a cell of size `z` other than `syscall`.
-/
import Spike.Lib.X64WakeWfN
import Spike.Lib.X64AllocGAb
import Spike.Lib.X64ThreadsAcSt
import Spike.Lib.X64WakeChild
import Spike.Lib.X64WakePh
import Spike.Lib.X64RelWS

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun)
open Spike.Lib.LowerX64 (blkLabs aiLab aiTgts_congr labC)
open Spike.Lib.X64.AllocG (blkAbC abLabs abPcs_congr blkAbC_congr)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Kraken.Promising.Lower.X64 (CellAt)

/-! ## The threads abort's labels -/

/-- **The labels `acPcs lab pfx` reads**: the spawn's, the dispatcher's and
the threads stub's. -/
def acLabs (pfx : String) : List String :=
  [pfx ++ ".x3", pfx ++ ".x4", pfx ++ ".spawnfail5", "scc_rt_abort", ".Lscc_rt_abort.entry",
    ".Lscc_rt_abort.next1", ".Lscc_rt_abort.next3", ".Lscc_rt_abort.next5", ".Lscc_rt_abort.next7",
    ".Lscc_rt_abort.is8", Spike.Lib.X64.Abort.threads.fn, Spike.Lib.X64.Abort.threads.entry,
    Spike.Lib.X64.Abort.threads.exit]

/-- **`acPcs` reads the labels of `acLabs` only.** -/
theorem acPcs_congr {lab lab' : Label → Int64} {pfx : String} (h : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    Spike.Lib.X64.ThreadsAb.acPcs lab pfx = Spike.Lib.X64.ThreadsAb.acPcs lab' pfx := by
  simp only [Spike.Lib.X64.ThreadsAb.acPcs, Spike.Lib.X64.ThreadsAb.pcRet, Spike.Lib.X64.ThreadsAb.pcJe,
    Spike.Lib.X64.ThreadsAb.cloneAt, Spike.Lib.X64.ThreadsAb.pcSt, Spike.Lib.X64.ThreadsAb.tailPcs,
    Spike.Lib.X64.ThreadsAb.failPcs, Spike.Lib.X64.WriteAb.dispEPcs, Spike.Lib.X64.ThreadsAb.dispTPcs,
    Spike.Lib.X64.ThreadsAb.g5Pcs, Spike.Lib.X64.ThreadsAb.stubPcs]
  rw [h (pfx ++ ".x3") (by simp [acLabs]),
    h (pfx ++ ".x4") (by simp [acLabs]),
    h (pfx ++ ".spawnfail5") (by simp [acLabs]),
    h ("scc_rt_abort") (by simp [acLabs]),
    h (".Lscc_rt_abort.entry") (by simp [acLabs]),
    h (".Lscc_rt_abort.next1") (by simp [acLabs]),
    h (".Lscc_rt_abort.next3") (by simp [acLabs]),
    h (".Lscc_rt_abort.next5") (by simp [acLabs]),
    h (".Lscc_rt_abort.next7") (by simp [acLabs]),
    h (".Lscc_rt_abort.is8") (by simp [acLabs]),
    h (Spike.Lib.X64.Abort.threads.fn) (by simp [acLabs]),
    h (Spike.Lib.X64.Abort.threads.entry) (by simp [acLabs]),
    h (Spike.Lib.X64.Abort.threads.exit) (by simp [acLabs])]

/-- `ThreadsAcSt.blkAc` (the same definition). -/
abbrev blkAcC (lab : Label → Int64) (pfx : String) (pc ra : Int64) (blk : List (Directive × Nat)) : Bool :=
  blkAc lab pfx pc ra blk

/-- **`blkAc` reads the labels at the block's targets and `acLabs` only.** -/
theorem blkAcC_congr {lab lab' : Label → Int64} {pfx : String} {pc ra : Int64} {blk : List (Directive × Nat)}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    blkAcC lab pfx pc ra blk = blkAcC lab' pfx pc ra blk := by
  unfold blkAcC blkAc
  rw [acPcs_congr ha]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc : Spike.Lib.X64.classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-! ## The checks -/

/-- **A block's targets off both phases' pcs**, the block at `lab l + k`
(bytes), its `ret`s to `lab rl`. -/
def phOff (lab : Label → Int64) (pfx : String) (l : Label) (k : Nat) (rl : Label)
    (blk : List (Directive × Nat)) : Bool :=
  blkAbC lab (lab l + Int64.ofNat k) (lab rl) blk && blkAcC lab pfx (lab l + Int64.ofNat k) (lab rl) blk

/-- **A single instruction's next pc off both phases' pcs**, the instruction
at `lab l + k` of size `z`. -/
def siOff (lab : Label → Int64) (pfx : String) (l : Label) (k z : Nat) : Bool :=
  !(Spike.Lib.X64.WriteAb.abPcs lab).contains (lab l + Int64.ofNat k + Int64.ofNat z) &&
    !(Spike.Lib.X64.ThreadsAb.acPcs lab pfx).contains (lab l + Int64.ofNat k + Int64.ofNat z)

/-- The labels `phOff` reads. -/
def phLabs (pfx : String) (l rl : Label) (blk : List (Directive × Nat)) : List String :=
  l :: rl :: blkLabs blk ++ abLabs ++ acLabs pfx

theorem phOff_congr {lab lab' : Label → Int64} {pfx : String} {l rl : Label} {k : Nat}
    {blk : List (Directive × Nat)}
    (h : ∀ x ∈ phLabs pfx l rl blk, lab x = lab' x) : phOff lab pfx l k rl blk = phOff lab' pfx l k rl blk := by
  unfold phOff
  have hb : ∀ x ∈ blkLabs blk, lab x = lab' x := fun x hx => h x (by simp [phLabs, hx])
  have ha : ∀ x ∈ abLabs, lab x = lab' x := fun x hx => h x (by simp [phLabs, hx])
  have hc : ∀ x ∈ acLabs pfx, lab x = lab' x := fun x hx => h x (by simp [phLabs, hx])
  rw [blkAbC_congr hb ha, blkAcC_congr hb hc, h l (by simp [phLabs]), h rl (by simp [phLabs])]

theorem siOff_congr {lab lab' : Label → Int64} {pfx : String} {l : Label} {k z : Nat}
    (h : ∀ x ∈ phLabs pfx l l [], lab x = lab' x) : siOff lab pfx l k z = siOff lab' pfx l k z := by
  unfold siOff
  rw [abPcs_congr fun x hx => h x (by simp [phLabs, hx]), acPcs_congr fun x hx => h x (by simp [phLabs, hx]),
    h l (by simp [phLabs])]

/-- **`phOff` at wake's code labels**, every label it reads resolving. -/
def phOffW (pfx : String) (l : Label) (k : Nat) (rl : Label) (blk : List (Directive × Nat)) : Bool :=
  (phLabs pfx l rl blk).all (fun x => (codeLabel Spike.Lib.X64.WakePh.lo wakeCells x).isSome) &&
    phOff (labC Spike.Lib.X64.WakePh.lo wakeCells) pfx l k rl blk

/-- **`siOff` at wake's code labels**, every label it reads resolving. -/
def siOffW (pfx : String) (l : Label) (k z : Nat) : Bool :=
  (phLabs pfx l l []).all (fun x => (codeLabel Spike.Lib.X64.WakePh.lo wakeCells x).isSome) &&
    siOff (labC Spike.Lib.X64.WakePh.lo wakeCells) pfx l k z

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a)
include hlab

/-- `lab` is the code labels at every resolving label of `xs`. -/
theorem lab_labC {xs : List String}
    (h : xs.all (fun x => (codeLabel Spike.Lib.X64.WakePh.lo wakeCells x).isSome) = true) :
    ∀ x ∈ xs, lab x = labC Spike.Lib.X64.WakePh.lo wakeCells x := fun x hx => by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h x hx)
  rw [hlab x y hy]; simp [labC, hy]

/-- **`phOffW` at any labels agreeing with the code labels.** -/
theorem phOffW_sound {pfx : String} {l rl : Label} {k : Nat} {blk : List (Directive × Nat)}
    (h : phOffW pfx l k rl blk = true) : phOff lab pfx l k rl blk = true := by
  simp only [phOffW, Bool.and_eq_true] at h
  rw [phOff_congr (lab_labC hlab h.1)]; exact h.2

/-- **`siOffW` at any labels agreeing with the code labels.** -/
theorem siOffW_sound {pfx : String} {l : Label} {k z : Nat} (h : siOffW pfx l k z = true) :
    siOff lab pfx l k z = true := by
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
theorem blkW_phSt {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l rl : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk j) → PcOff μ s)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (h : phOff (_root_.Executable.labels exe).label pfx l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = (_root_.Executable.labels exe).label rl) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.X64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  simp only [phOff, Bool.and_eq_true, he] at h
  exact BlkW.and (blkW_abSt hcode hok hR hlo hhi hpc (blkAb_sound h.1 hret))
    (blkW_acStN hcode hok hR hlo hhi hpc (blkAc_sound h.2 hret))

/-- **A single instruction's states keep both phases**: a cell of size `z`
other than a `syscall` whose leaves are `z` bytes on (`hstep`), off the take
site (`htk`), its next pc off both phases' pcs (`h`). -/
theorem nodeW_phSt {n : ND} {l : Label} {k z : Nat}
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (h : siOff (_root_.Executable.labels exe).label pfx l k z = true)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.X64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hA
  simp only [siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hsys : abi.atSys s = false := atSyscall_false_of_cellAt hc hd
  have htk' : ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha => by
    unfold pcOf; rw [hpc]; exact htk a ha
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.X64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h.1)
  have hnac : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.X64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s' :=
    fun s' hs' => Spike.Lib.X64.ThreadsAb.not_ac_of_pc (by rw [hl s' hs', hpc]; exact h.2)
  refine ⟨⟨AbSt.ofLeaves htk' hsys fun t ht => ?_, AcSt.ofLeaves htk' hsys fun _ t ht => ?_⟩, fun _ h => h⟩
  · rw [hex] at ht; cases ht; exact allInv_of_leaf tree hnab
  · rw [hex] at ht; cases ht; exact allInv_of_leaf tree hnac

end Nodes

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.acPcs_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.acPcs_congr

/-- info: 'Spike.Lib.X64.WakeWf.blkAcC_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkAcC_congr

/-- info: 'Spike.Lib.X64.WakeWf.phOff_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.phOff_congr

/-- info: 'Spike.Lib.X64.WakeWf.siOff_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.siOff_congr

/-- info: 'Spike.Lib.X64.WakeWf.lab_labC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.lab_labC

/-- info: 'Spike.Lib.X64.WakeWf.phOffW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.phOffW_sound

/-- info: 'Spike.Lib.X64.WakeWf.siOffW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.siOffW_sound

/-- info: 'Spike.Lib.X64.WakeWf.blkW_phSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_phSt

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_phSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_phSt
