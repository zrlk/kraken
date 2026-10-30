/-
**Pcs of runs off given pcs, decided on the listing** (AArch64, the listing facts at an instance): every pc `label l + 4j` of a list of
runs `(l, lo, hi)` differs from every pc `label l' + 4k'` of a list of
points, in any executable laying out the program (`Lays`), decided on the
directive list alone (`runsNeChk`, by `decide +kernel` at the program), by
the instructions' indices: in a valid layout, distinct instructions have
distinct addresses (`PcRuns.addrOf_inj`). Generic in the program: a new
listing only re-runs the decisions.

- `nthIns`, `insIdx prog l j`: the index of the instruction at `label l + 4j`
  (labels skipped, as they take no bytes: a run may cross a label).
- `runsNeChk prog runs pts`: every point's and run pc's instruction exists,
  and no run pc's index is a point's.
- `label_insIdx`: `label l + 4j` is the address of the instruction cell
  `insIdx prog l j`; `label_add_ne`: distinct indices, distinct pcs.
- `runsNe_of_chk`: the runs' pcs are none of the points' (the label-relative
  form of `RunsNe`).
- `abPtsA`: the seven labels of `A64WakeOff.PcOffA` (the five abort exits and
  the two transfer sites) at count `0`; `runsOffA_of_chk`:
  `A64WakeOff.RunsOffA` from `runsNeChk prog runs abPtsA`.
-/
import Spike.Lib.A64PcRuns
import Spike.Lib.A64WakeOffDef

namespace Spike.Lib.A64.RunsOff

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays labelIdx)
open Spike.Lib.A64.PcRuns (addrOf_inj)
open Spike.Lib.A64WakeOff (PcOffA RunsOffA)

/-- **The offset of the `j`-th instruction** of a directive list, labels
skipped (they take no bytes), stopping at data. -/
def nthIns : List Directive → Nat → Option Nat
  | [], _ => none
  | .instr _ :: _, 0 => some 0
  | .instr _ :: ds, j + 1 => (nthIns ds j).map (· + 1)
  | .label _ :: ds, j => (nthIns ds j).map (· + 1)
  | .byteArray _ :: _, _ => none

/-- **The index of the instruction at `label l + 4j`**: the `j`-th
instruction after the first `label l`, labels skipped. -/
def insIdx (prog : List Directive) (l : Label) (j : Nat) : Option Nat :=
  match labelIdx prog l with
  | some i => (nthIns (prog.drop (i + 1)) j).map (i + 1 + ·)
  | none => none

/-- **The runs' pcs are none of the points'**, by index: every point's and
every run pc's instruction exists (`insIdx` is some), and no run pc's is a
point's. -/
def runsNeChk (prog : List Directive) (runs : List (Label × Nat × Nat)) (pts : List (Label × Nat)) : Bool :=
  pts.all (fun p => (insIdx prog p.1 p.2).isSome) && runs.all fun r =>
    (List.range r.2.2).all fun j => !decide (r.2.1 ≤ j) ||
      ((insIdx prog r.1 j).isSome && pts.all fun p => insIdx prog r.1 j != insIdx prog p.1 p.2)

section Addr

variable {exe : _root_.Executable} [hv : Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}

theorem ofNat4_succ (a : Int64) (j : Nat) :
    a + Int64.ofNat 4 + Int64.ofNat (4 * j) = a + Int64.ofNat (4 * (j + 1)) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add, show 4 + 4 * j = 4 * (j + 1) by omega]

/-- **The `j`-th instruction after cell `s`** is an instruction cell, `4j`
bytes after cell `s`. -/
theorem addr_nthIns (hp : Lays exe prog kp) :
    ∀ (ds : List Directive) (s j m : Nat), prog.drop s = ds → nthIns ds j = some m →
      (∃ ins z, exe.2[kp + (s + m)]? = some (.instr ins, z)) ∧
        Kraken.Executable.addrOf exe (kp + (s + m)) = Kraken.Executable.addrOf exe (kp + s) + Int64.ofNat (4 * j)
  | [], _, _, _, _, h => by simp [nthIns] at h
  | d :: ds, s, j, m, hd, h => by
    have hs : prog[s]? = some d := by
      have := congrArg (·[0]?) hd
      simpa [List.getElem?_drop] using this
    have hds : prog.drop (s + 1) = ds := by rw [← List.tail_drop, hd]; rfl
    obtain ⟨z, hz⟩ := Scc.Cert.Rt.A64.getElem?_fst hp hs
    have hsucc := Kraken.Executable.addrOf_succ exe hz
    rw [show kp + s + 1 = kp + (s + 1) by omega] at hsucc
    cases d with
    | instr ins =>
      cases j with
      | zero =>
        simp only [nthIns, Option.some.injEq] at h
        subst h
        exact ⟨⟨ins, z, by simpa using hz⟩, by rw [Nat.add_zero, show Int64.ofNat (4 * 0) = 0 by decide, Int64.add_zero]⟩
      | succ j =>
        simp only [nthIns, Option.map_eq_some_iff] at h
        obtain ⟨m', hm', rfl⟩ := h
        obtain ⟨hc, ha⟩ := addr_nthIns hp ds (s + 1) j m' hds hm'
        have hz4 := hv.instr_size _ ins z hz
        subst hz4
        refine ⟨by rw [show s + (m' + 1) = s + 1 + m' by omega]; exact hc, ?_⟩
        rw [show s + (m' + 1) = s + 1 + m' by omega, ha, hsucc, ofNat4_succ]
    | label l =>
      simp only [nthIns, Option.map_eq_some_iff] at h
      obtain ⟨m', hm', rfl⟩ := h
      obtain ⟨hc, ha⟩ := addr_nthIns hp ds (s + 1) j m' hds hm'
      have hz0 := hv.label_size _ l z hz
      subst hz0
      refine ⟨by rw [show s + (m' + 1) = s + 1 + m' by omega]; exact hc, ?_⟩
      rw [show s + (m' + 1) = s + 1 + m' by omega, ha, hsucc, show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
    | byteArray _ => simp [nthIns] at h

/-- **`label l + 4j` is the address of the instruction cell `insIdx`.** -/
theorem label_insIdx (hp : Lays exe prog kp) {l : Label} {j n : Nat} (h : insIdx prog l j = some n) :
    (∃ ins z, exe.2[kp + n]? = some (.instr ins, z)) ∧
      (_root_.Executable.labels exe).label l + Int64.ofNat (4 * j) = Kraken.Executable.addrOf exe (kp + n) := by
  unfold insIdx at h
  split at h
  next i hi =>
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hc, ha⟩ := addr_nthIns hp _ (i + 1) j m rfl hm
    obtain ⟨hpi, hfi⟩ := Scc.Cert.Rt.A64.labelIdx_spec hi
    obtain ⟨z, hz⟩ := Scc.Cert.Rt.A64.getElem?_fst hp hpi
    have hz0 := hv.label_size _ l z hz
    subst hz0
    have hsucc := Kraken.Executable.addrOf_succ exe hz
    rw [show kp + i + 1 = kp + (i + 1) by omega, show Int64.ofNat 0 = 0 by decide, Int64.add_zero] at hsucc
    refine ⟨by rw [show i + 1 + m = (i + 1) + m from rfl]; exact hc, ?_⟩
    rw [Kraken.Executable.label_addrOf exe l _ hz (hp.first hpi hfi), ← hsucc, ← ha]
  next => cases h

/-- **Two pcs with distinct instruction indices are distinct.** -/
theorem label_add_ne (hp : Lays exe prog kp) {l l' : Label} {k k' : Nat}
    (hl : (insIdx prog l k).isSome) (hl' : (insIdx prog l' k').isSome)
    (hne : insIdx prog l k ≠ insIdx prog l' k') :
    (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) ≠
      (_root_.Executable.labels exe).label l' + Int64.ofNat (4 * k') := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hl'
  obtain ⟨⟨_, _, hc⟩, ha⟩ := label_insIdx hp hn
  obtain ⟨⟨_, _, hc'⟩, ha'⟩ := label_insIdx hp hn'
  intro h
  rw [ha, ha'] at h
  have := addrOf_inj hc hc' h
  apply hne
  rw [hn, hn']
  congr 1
  omega

/-- **The runs' pcs are none of the points'** (`runsNeChk`). -/
theorem runsNe_of_chk (hp : Lays exe prog kp) {runs : List (Label × Nat × Nat)} {pts : List (Label × Nat)}
    (h : runsNeChk prog runs pts = true) :
    ∀ r ∈ runs, ∀ j, r.2.1 ≤ j → j < r.2.2 → ∀ p ∈ pts,
      (_root_.Executable.labels exe).label r.1 + Int64.ofNat (4 * j) ≠
        (_root_.Executable.labels exe).label p.1 + Int64.ofNat (4 * p.2) := by
  simp only [runsNeChk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hpts, hruns⟩ := h
  intro r hr j hlo hhi p hpm
  have hj := hruns r hr j (List.mem_range.mpr hhi)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true, List.all_eq_true,
    bne_iff_ne] at hj
  rcases hj with h1 | ⟨h1, h2⟩
  · exact absurd hlo h1
  · exact label_add_ne hp h1 (hpts p hpm) (h2 p hpm)

end Addr

/-- **The labels of `PcOffA`** at count `0`: the five abort exits and the two
transfer sites. -/
def abPtsA : List (Label × Nat) :=
  [("scc_rt_abort_overflow_exit", 0), ("scc_rt_abort_heap_exit", 0), ("scc_rt_abort_stack_exit", 0),
    ("scc_rt_abort_write_exit", 0), ("scc_rt_abort_threads_exit", 0), ("scc_rt_take_site", 0),
    ("scc_rt_release_site", 0)]

/-- **`RunsOffA` decided on the listing**: the runs' pcs are none of
`abPtsA`'s. -/
theorem runsOffA_of_chk {exe : _root_.Executable} [Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) {runs : List (Label × Nat × Nat)} (h : runsNeChk prog runs abPtsA = true) :
    RunsOffA (_root_.Executable.labels exe).label runs := by
  intro r hr j hlo hhi
  have hne := runsNe_of_chk hp h r hr j hlo hhi
  have z : ∀ a : Int64, a + Int64.ofNat (4 * 0) = a := fun a => by
    rw [show Int64.ofNat (4 * 0) = 0 by decide, Int64.add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq
  · exact hne ("scc_rt_abort_overflow_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_heap_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_stack_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_write_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_threads_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_take_site", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_release_site", 0) (by simp [abPtsA]) (by simpa only [z] using heq)

/-- info: 'Spike.Lib.A64.RunsOff.runsNe_of_chk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runsNe_of_chk

/-- info: 'Spike.Lib.A64.RunsOff.runsOffA_of_chk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runsOffA_of_chk

end Spike.Lib.A64.RunsOff
