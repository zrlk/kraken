/-
**The pushed return address at the dispatcher's targets** (x86-64): the
threads abort holds at the dispatcher's pcs only with its return address
`raT` pushed (`ThreadsAb.RaW`), read at `0(%rsp)`, `8(%rsp)` or `8(%rbp)` by
the pc. One check per block (`rChk`, decided at the cells' code labels as
`X64WakeWfAb`'s `dChk` is) names, for each instruction, where its targets
read the word: past an instruction in `S` the word is at `0(%rsp)`, in `P` at
`8(%rsp)`, in `B` at `8(%rbp)`. With the abstract run's offsets putting
`slot 8` there and `slot 8` not `raT`, no target is in the threads abort by
its return address (`hX_of`, `blkW_dispPh`'s `hX`).

- `raLabs`, `rOk`, `rChk`: the check and the labels it reads.
- `raPcs_congr`, `rOk_congr`, `rChk_congr`, `rLabs`, `rChkW`,
  `rChkW_sound`: the check at the code labels moved to any labels agreeing.
- `hX_of`: `blkW_dispPh`'s `hX` from the check and the run's data.

No AArch64 counterpart: there the return address is `x30`, a register of
the abstract state, and `hX` is a fact of the abstract run alone.
-/
import Spike.Lib.X64WakeWfHP

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64Consumer (aiTgts)
open Spike.Lib.X64 (cellOff arun classify Abs ND)
open Spike.Lib.LowerX64 (blkLabs aiTgts_congr labC)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)

/-! ## The check -/

/-- The labels `RaW`'s pcs read: the dispatcher's and the threads stub's. -/
def raLabs : List String :=
  ["scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.next1", ".Lscc_rt_abort.next3",
    ".Lscc_rt_abort.next5", ".Lscc_rt_abort.next7", ".Lscc_rt_abort.is8", Spike.Lib.X64.Abort.threads.fn,
    Spike.Lib.X64.Abort.threads.entry, Spike.Lib.X64.Abort.threads.exit]

/-- **A target `t` of instruction `k` reading the pushed word where the run
puts it**: at a pc of `raSPcs` only if `k ∈ S`, of `raPPcs` only if `k ∈ P`,
of `raBPcs` only if `k ∈ B`. -/
def rOk (lab : Label → Int64) (S P B : List Nat) (k : Nat) (t : Int64) : Bool :=
  (!(ThreadsAb.raSPcs lab).contains t || S.contains k) && (!(ThreadsAb.raPPcs lab).contains t || P.contains k) &&
    (!(ThreadsAb.raBPcs lab).contains t || B.contains k)

/-- **Every target of a block passing `rOk`**, the block at `pc`. -/
def rChk (lab : Label → Int64) (pc : Int64) (S P B : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) 0 a).all (rOk lab S P B k)
      | none => false
    | none => false

/-! ## The labels it reads -/

section Congr

variable {lab lab' : Label → Int64}

theorem raPcs_congr (h : ∀ l ∈ raLabs, lab l = lab' l) :
    ThreadsAb.raSPcs lab = ThreadsAb.raSPcs lab' ∧ ThreadsAb.raPPcs lab = ThreadsAb.raPPcs lab' ∧
      ThreadsAb.raBPcs lab = ThreadsAb.raBPcs lab' := by
  simp (disch := decide) only [ThreadsAb.raSPcs, ThreadsAb.raPPcs, ThreadsAb.raBPcs, ThreadsAb.dispTPcs,
    ThreadsAb.stubPcs, h, and_self]

theorem rOk_congr {S P B : List Nat} (h : ∀ l ∈ raLabs, lab l = lab' l) : rOk lab S P B = rOk lab' S P B := by
  obtain ⟨h1, h2, h3⟩ := raPcs_congr h
  unfold rOk
  rw [h1, h2, h3]

theorem rChk_congr {pc : Int64} {S P B : List Nat} {blk : List (Directive × Nat)}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (hr : ∀ l ∈ raLabs, lab l = lab' l) :
    rChk lab pc S P B blk = rChk lab' pc S P B blk := by
  unfold rChk
  rw [rOk_congr hr]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc' : classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc']; exact hL⟩

end Congr

/-- The labels `rChk` reads, the block at `l`. -/
def rLabs (l : Label) (blk : List (Directive × Nat)) : List String :=
  l :: blkLabs blk ++ raLabs

/-- **`rChk` at wake's code labels**, every label it reads resolving, the
block at `lab l + k` (bytes). -/
def rChkW (l : Label) (k : Nat) (S P B : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (rLabs l blk).all (fun x => (codeLabel Spike.Lib.X64.WakePh.lo wakeCells x).isSome) &&
    rChk (labC Spike.Lib.X64.WakePh.lo wakeCells) (labC Spike.Lib.X64.WakePh.lo wakeCells l + Int64.ofNat k)
      S P B blk

/-- **`rChkW` at any labels agreeing with the code labels.** -/
theorem rChkW_sound {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a)
    {l : Label} {k : Nat} {S P B : List Nat} {blk : List (Directive × Nat)}
    (h : rChkW l k S P B blk = true) : rChk lab (lab l + Int64.ofNat k) S P B blk = true := by
  simp only [rChkW, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [rChk_congr (fun x hx => hl x (by simp [rLabs, hx])) (fun x hx => hl x (by simp [rLabs, hx])),
    hl l (by simp [rLabs])]
  exact h.2

/-! ## The return address kept off `raT` -/

/-- **`blkW_dispPh`'s `hX` from the check**: past instruction `k` the run's
offsets put `slot 8` where each target reads the pushed word (`hS`, `hP`,
`hB`, `R.Off 8`), and `slot 8` is not `raT` (`hra`). -/
theorem hX_of {lab : Label → Int64} {pfx : String} {R : Region} {n : ND} {blk : List (Directive × Nat)}
    {S P B : List Nat} (h : rChk lab n.pc S P B blk = true) (hoff : R.Off 8)
    (hS : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ S →
      (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp = 8)
    (hP : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ P →
      (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp = 0)
    (hB : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ B →
      (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.get .rbp = some 0)
    (hra : ∀ σ c, n.J σ c → ∀ k, k < blk.length →
      (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot 8 ≠ ThreadsAb.raT lab pfx) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → ∀ s' : State,
      s'.st.2 ∈ aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a →
      Abs R (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1 (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ ThreadsAb.RaW lab s' (ThreadsAb.raT lab pfx) := by
  intro σ c hJ k hk a ha s' hs' hA hW
  have hk' := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at hk'
  have hr := List.all_eq_true.mp hk' _ hs'
  simp only [rOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, decide_eq_true_eq] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  exact hra σ c hJ k hk (raW_slot hA hoff
    (fun m => hS σ c hJ k hk (h1.resolve_left fun hn => hn m))
    (fun m => hP σ c hJ k hk (h2.resolve_left fun hn => hn m))
    (fun m => hB σ c hJ k hk (h3.resolve_left fun hn => hn m)) hW)

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.rChkW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.rChkW_sound

/-- info: 'Spike.Lib.X64.WakeWf.hX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.hX_of
