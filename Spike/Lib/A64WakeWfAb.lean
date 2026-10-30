/-
**wake.w's two abort phases kept at the dispatcher's blocks by their data**
(`Wf`'s `AbSt`/`AcSt`, AArch64): the dispatcher's prologue and tests reach
pcs of both phases (`WriteAb.dispEPcs`/`dispTPcs`, the threads abort's
same pcs), where the write abort holds only at the code `4` (in `x0`, then
at `[sp]`) and the threads abort only at `x30 = raT`. A path entering the
dispatcher with another code and another return address keeps both phases
out: one check per block (`dChk`, decided at the program's code labels as
`A64WakeWfPh`'s checks are) puts every target off the phases' other pcs
and names the instructions whose targets may be at the prologue's (`E`)
or the tests' (`T`) pcs, where the node's data must keep the code off `4`.

- `spPcs`, `tOk`, `dChk`: the check.
- `nvPcs_congr'`, `dispEPcs_congr`, `dispTPcs_congr`, `spPcs_congr`,
  `tOk_congr`, `dChk_congr`, `dLabs`, `dChkW`, `dChkW_sound`: the labels it
  reads, and the check at the code labels moved to any labels agreeing.
- `blkW_dispPh`: a covered block's states in `AbSt ∧ AcSt` from `dChk` and
  the data past each instruction (`hE`, `hT`, `hX`).
-/
import Spike.Lib.A64WakeWfPh
import Spike.Lib.LowerA64.StubAbW2

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.LowerA64 (blkLabs aiLab aiTgts_congr labC nvPcs arun_succ_eq sp_slot)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.A64.WriteAb (spLoad dispEPcs dispTPcs)
open Scc.Cert.Link.A64 (codeOf)

/-! ## The check -/

/-- The spawn's own pcs of the threads abort (`ThreadsAb.ac_x30`'s). -/
def spPcs (lab : Label → Int64) (pfx : String) : List Int64 :=
  ThreadsAb.pcRet lab pfx :: ThreadsAb.pcSt lab pfx :: ThreadsAb.tailPcs lab pfx ++ ThreadsAb.failPcs lab pfx

/-- **A target of instruction `k` off both phases but by data**: off the
write abort's pcs without a data condition and the spawn's, at the
prologue's pcs only if `k ∈ E`, at the tests' only if `k ∈ T`. -/
def tOk (lab : Label → Int64) (pfx : String) (E T : List Nat) (k : Nat) (t : Int64) : Bool :=
  !(nvPcs lab).contains t && (E.contains k || !(dispEPcs lab).contains t) &&
    (T.contains k || !(dispTPcs lab).contains t) && !(spPcs lab pfx).contains t

/-- **A block's targets off both phases but by data** (`tOk`), the block at
`pc`, without a `ret`. -/
def dChk (lab : Label → Int64) (pfx : String) (pc : Int64) (E T : List Nat) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) 0 a).all (tOk lab pfx E T k)
      | none => false
    | none => false

/-! ## The labels it reads -/

section Congr

variable {lab lab' : Label → Int64} {pfx : String}

theorem nvPcs_congr' (h : ∀ l ∈ abLabs, lab l = lab' l) : nvPcs lab = nvPcs lab' := by
  simp (disch := decide) only [nvPcs, WriteAb.pcRet, Spike.Lib.A64.PrintD.pcSvc, WriteAb.tailPcs,
    WriteAb.failPcs, WriteAb.g4Pcs, WriteAb.stubPcs, h]

theorem dispEPcs_congr (h : ∀ l ∈ abLabs, lab l = lab' l) : dispEPcs lab = dispEPcs lab' := by
  simp (disch := decide) only [dispEPcs, h]

theorem dispTPcs_congr (h : ∀ l ∈ abLabs, lab l = lab' l) : dispTPcs lab = dispTPcs lab' := by
  simp (disch := decide) only [dispTPcs, h]

theorem spPcs_congr (h : ∀ l ∈ acLabs pfx, lab l = lab' l) : spPcs lab pfx = spPcs lab' pfx := by
  simp only [spPcs, ThreadsAb.pcRet, ThreadsAb.cloneAt, ThreadsAb.pcSt, ThreadsAb.tailPcs, ThreadsAb.failPcs]
  rw [h _ (by simp [acLabs] : pfx ++ ".sp6" ∈ acLabs pfx), h _ (by simp [acLabs] : pfx ++ ".clone9" ∈ acLabs pfx),
    h _ (by simp [acLabs] : pfx ++ ".1_spawnfail5" ∈ acLabs pfx)]

theorem tOk_congr {E T : List Nat} (ha : ∀ l ∈ abLabs, lab l = lab' l) (hc : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    tOk lab pfx E T = tOk lab' pfx E T := by
  unfold tOk
  rw [nvPcs_congr' ha, dispEPcs_congr ha, dispTPcs_congr ha, spPcs_congr hc]

theorem dChk_congr {pc : Int64} {E T : List Nat} {blk : List Directive} (h : ∀ L ∈ blkLabs blk, lab L = lab' L)
    (ha : ∀ l ∈ abLabs, lab l = lab' l) (hc : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    dChk lab pfx pc E T blk = dChk lab' pfx pc E T blk := by
  unfold dChk
  rw [tOk_congr ha hc]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc' : Spike.Lib.A64.Flow.classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc']; exact hL⟩

end Congr

/-- The labels `dChk` reads, the block at `l`. -/
def dLabs (pfx : String) (l : Label) (blk : List Directive) : List String :=
  l :: blkLabs blk ++ abLabs ++ acLabs pfx

/-- **`dChk` at wake's code labels**, every label it reads resolving, the
block at `lab l + 4 k`. -/
def dChkW (pfx : String) (l : Label) (k : Nat) (E T : List Nat) (blk : List Directive) : Bool :=
  (dLabs pfx l blk).all (fun x => (codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x).isSome) &&
    dChk (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg) pfx
      (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l + Int64.ofNat (4 * k)) E T blk

/-- **`dChkW` at any labels agreeing with the code labels.** -/
theorem dChkW_sound {lab : Label → Int64}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x → lab l = Int64.ofNat x)
    {pfx : String} {l : Label} {k : Nat} {E T : List Nat} {blk : List Directive}
    (h : dChkW pfx l k E T blk = true) : dChk lab pfx (lab l + Int64.ofNat (4 * k)) E T blk = true := by
  simp only [dChkW, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [dChk_congr (fun x hx => hl x (by simp [dLabs, hx])) (fun x hx => hl x (by simp [dLabs, hx]))
    (fun x hx => hl x (by simp [dLabs, hx])), hl l (by simp [dLabs])]
  exact h.2

/-! ## The phases kept at a dispatcher block -/

section Blk

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {pfx : String}

/-- **A dispatcher block's states keep both phases**: a covered block
without a `ret` (`hnr`), its pcs off the marks' sites (`hpc`), its targets
off both phases but by data (`h`), the data past instruction `k` keeping
the code off `4` in `x0` for `k ∈ E` (`hE`) and at `[sp]` for `k ∈ T`
(`hT`), and `x30` off `raT` (`hX`). -/
theorem blkW_dispPh {n : ND} {blk : List Directive} {lo hi : Int} {E T : List Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-32))
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (hnr : noRetBlk blk = true)
    (h : dChk (_root_.Executable.labels exe).label pfx n.pc E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.X0
        ≠ 4)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp
        = -32 ∧
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot
        (-32) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
        ⟨n.pc, n.o, σ⟩).σ.regs.X30.toBitVec ≠ ThreadsAb.raT (_root_.Executable.labels exe).label pfx) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  have key : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a →
      ∀ s' : State, s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' ∧
        ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s' := by
    intro σ c hJ k hk a ha s' hpc' hA'
    have hc := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    simp only [List.getElem?_eq_getElem hk, ha] at hc
    have ht := List.all_eq_true.mp hc _ (aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (fall := n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) (ra := 0)
      (σ := (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      fun r hr => (noRet_false hnr k hk r (hr ▸ ha)).elim)
    rw [← hpc'] at ht
    simp only [tOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_true_eq, decide_eq_false_iff_not] at ht
    obtain ⟨⟨⟨hnv, hE'⟩, hT'⟩, hsp⟩ := ht
    refine ⟨?_, fun hac => ?_⟩
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨h1, h4⟩ | ⟨h1, h4⟩ | h1 | h1)
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
      · rcases hE' with hk' | hk'
        · exact hE σ c hJ k hk hk' (by rw [hA'.regs] at h4; exact h4)
        · exact hk' h1
      · rcases hT' with hk' | hk'
        · obtain ⟨hs, hsl⟩ := hT σ c hJ k hk hk'
          rw [sp_slot hA' hs hoff] at h4
          exact hsl (Option.some.inj h4)
        · exact hk' h1
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
    · have hx := ThreadsAb.ac_x30 hac (by simpa [spPcs] using hsp)
      rw [hA'.regs] at hx
      exact hX σ c hJ k hk hx
  refine BlkW.and (blkW_abSt hcode hok hR hal hlo hhi hpc ?_) (blkW_acStN hcode hok hR hal hlo hhi hpc ?_)
  · intro σ c hJ k hk a ha s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').1
  · intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').2

end Blk

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.dChkW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.dChkW_sound

/-- info: 'Spike.Lib.A64.WakeWf.blkW_dispPh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.blkW_dispPh
