/-
**Pcs of byte runs off given pcs, decided on the listing** (x86-64): the x64 twin of
`Spike/Lib/A64RunsOff.lean`. Every pc `label l + j`
of a list of byte runs `(l, lo, hi)` differs from every pc `label l' + k'`
of a list of points, in any executable laying out the code cells (`Lays`),
decided on the cell list alone (`runsNeChk`, by `decide +kernel` at the
certificate's cells), by byte offsets: under `Lays exe cells kp`,
`label l` is `exe.1` plus the bytes of the first `kp` cells plus `l`'s
offset in `cells` (`labOff`), and the layout does not wrap (`no_wrap`), so
two pcs within the cells are equal exactly when their offsets are. Generic
in the program: a new listing only re-runs the decisions.

x86-64 instructions have no fixed size, so where AArch64 counts
instructions (`label l + 4j`, by instruction indices), here the runs are
byte ranges (`X64AbOffLDef`'s runs) and the check compares intervals of
offsets, with no per-byte loop.

- `labOff cells l`: the bytes before the first `label l` in `cells`.
- `runsNeChk cells runs pts`: every run's and point's label is in `cells`,
  within its bytes, and no run's byte range meets a point.
- `label_labOff`: `label l = exe.1 + (bytes of the first kp cells + labOff)`.
- `runsNe_of_chk`: the runs' pcs are none of the points'.
- `abPtsA`: the seven labels of `X64WakeOff.PcOffA` (the five abort exits and
  the two transfer sites) at offset `0`; `runsOffA_of_chk`:
  `X64WakeOff.RunsOffA` from `runsNeChk cells runs abPtsA`.
-/
import Scc.Cert.Rt.LaysX64
import Spike.Lib.X64WakeOffDef

namespace Spike.Lib.X64.RunsOff

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays labelIdx labelIdx_spec)
open Spike.Lib.X64WakeOff (PcOffA RunsOffA)

/-- **The bytes before the first `label l`** of the cells. -/
def labOff (cells : List (Directive × Nat)) (l : Label) : Option Nat :=
  (labelIdx cells l).map fun i => ((cells.take i).map (·.2)).sum

/-- **The runs' byte ranges miss the points**: every run's and point's label
is in `cells` and its offsets are within `cells`' bytes, and no run's byte
range `[off l + lo, off l + hi)` holds a point's `off l' + k'`. -/
def runsNeChk (cells : List (Directive × Nat)) (runs : List (Label × Nat × Nat)) (pts : List (Label × Nat)) :
    Bool :=
  let tot := (cells.map (·.2)).sum
  pts.all (fun p => match labOff cells p.1 with
    | some b => decide (b + p.2 ≤ tot)
    | none => false) &&
  runs.all fun r => match labOff cells r.1 with
    | some a => decide (a + r.2.2 ≤ tot) && pts.all fun p => match labOff cells p.1 with
      | some b => !(decide (a + r.2.1 ≤ b + p.2) && decide (b + p.2 < a + r.2.2))
      | none => false
    | none => false

section Addr

variable {exe : _root_.Executable} [hv : Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **A label of `cells` is at its offset**: `exe.1` plus the bytes of the
first `kp` cells and of `cells` before it. -/
theorem label_labOff (hp : Lays exe cells kp) {l : Label} {a : Nat} (h : labOff cells l = some a) :
    (_root_.Executable.labels exe).label l =
      exe.1 + Int64.ofNat (((exe.2.take kp).map (·.2)).sum + a) ∧
      a ≤ (cells.map (·.2)).sum := by
  unfold labOff at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨⟨z, hz⟩, hf⟩ := labelIdx_spec hi
  have hil : i ≤ cells.length := by
    rcases Nat.lt_or_ge i cells.length with hc | hc
    · exact Nat.le_of_lt hc
    · rw [List.getElem?_eq_none hc] at hz; cases hz
  have he := hp.getElem? hz
  have hz0 := hv.label_size _ l z he
  subst hz0
  refine ⟨?_, ?_⟩
  · rw [Kraken.Executable.label_addrOf exe l _ he (hp.first hz hf)]
    unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
    rw [hp.take_add hil, List.map_append, List.sum_append]
  · conv => rhs; rw [← List.take_append_drop i cells]
    simp only [List.map_append, List.sum_append]
    omega

/-- The bytes of the first `kp` cells and of `cells` are within the
executable's, so below `2 ^ 64`. -/
theorem base_add_lt (hp : Lays exe cells kp) :
    ((exe.2.take kp).map (·.2)).sum + (cells.map (·.2)).sum < 2 ^ 64 := by
  have hcs : ((exe.2.take kp).map (·.2)).sum + (cells.map (·.2)).sum ≤ (exe.2.map (·.2)).sum := by
    obtain ⟨pre, ext, hx, rfl, -⟩ := hp
    rw [hx, List.append_assoc, List.take_left, List.map_append, List.map_append, List.sum_append,
      List.sum_append]; omega
  have := hv.no_wrap
  omega

/-- **Two pcs at offsets within the cells are equal only at equal
offsets.** -/
theorem label_add_ne (hp : Lays exe cells kp) {l l' : Label} {a b j k : Nat} (ha : labOff cells l = some a)
    (hb : labOff cells l' = some b) (hj : a + j ≤ (cells.map (·.2)).sum) (hk : b + k ≤ (cells.map (·.2)).sum)
    (hne : a + j ≠ b + k) :
    (_root_.Executable.labels exe).label l + Int64.ofNat j ≠ (_root_.Executable.labels exe).label l' + Int64.ofNat k := by
  rw [(label_labOff hp ha).1, (label_labOff hp hb).1]
  have hB := base_add_lt hp
  intro heq
  have h4 := congrArg Int64.toBitVec heq
  simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat', BitVec.add_assoc] at h4
  have h5 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h4)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h5
  rw [Nat.mod_eq_of_lt (a := _ + a) (by omega), Nat.mod_eq_of_lt (a := _ + b) (by omega),
    Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
  omega

/-- **The runs' pcs are none of the points'** (`runsNeChk`). -/
theorem runsNe_of_chk (hp : Lays exe cells kp) {runs : List (Label × Nat × Nat)} {pts : List (Label × Nat)}
    (h : runsNeChk cells runs pts = true) :
    ∀ r ∈ runs, ∀ j, r.2.1 ≤ j → j < r.2.2 → ∀ p ∈ pts,
      (_root_.Executable.labels exe).label r.1 + Int64.ofNat j ≠
        (_root_.Executable.labels exe).label p.1 + Int64.ofNat p.2 := by
  simp only [runsNeChk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hpts, hruns⟩ := h
  intro r hr j hlo hhi p hpm
  have hr' := hruns r hr
  have hp' := hpts p hpm
  split at hr'
  next a ha =>
    split at hp'
    next b hb =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr' hp'
      obtain ⟨hra, hrp⟩ := hr'
      have hx := hrp p hpm
      rw [hb] at hx
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx
      refine label_add_ne hp ha hb (by omega) hp' ?_
      omega
    next => simp at hp'
  next => simp at hr'

end Addr

/-- **The labels of `PcOffA`** at offset `0`: the five abort exits and the two
transfer sites. -/
def abPtsA : List (Label × Nat) :=
  [("scc_rt_abort_overflow_exit", 0), ("scc_rt_abort_heap_exit", 0), ("scc_rt_abort_stack_exit", 0),
    ("scc_rt_abort_write_exit", 0), ("scc_rt_abort_threads_exit", 0), ("scc_rt_take_site", 0),
    ("scc_rt_release_site", 0)]

/-- **`RunsOffA` decided on the listing**: the runs' pcs are none of
`abPtsA`'s. -/
theorem runsOffA_of_chk {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) {runs : List (Label × Nat × Nat)} (h : runsNeChk cells runs abPtsA = true) :
    RunsOffA (_root_.Executable.labels exe).label runs := by
  intro r hr j hlo hhi
  have hne := runsNe_of_chk hp h r hr j hlo hhi
  have z : ∀ a : Int64, a + Int64.ofNat 0 = a := fun a => by
    rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq
  · exact hne ("scc_rt_abort_overflow_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_heap_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_stack_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_write_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_threads_exit", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_take_site", 0) (by simp [abPtsA]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_release_site", 0) (by simp [abPtsA]) (by simpa only [z] using heq)

/-- **The four labels of `X64AbOffL.PcOff`** at offset `0`. -/
def abPts : List (Label × Nat) :=
  [("scc_rt_abort_write_exit", 0), ("scc_rt_abort_threads_exit", 0), ("scc_rt_take_site", 0),
    ("scc_rt_release_site", 0)]

/-- **`X64AbOffL.RunsOff` decided on the listing** (`ParkW`'s `hW`, the
segments' `W` checks): the runs' pcs are none of `abPts`'. -/
theorem runsOff_of_chk {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) {runs : List (Label × Nat × Nat)} (h : runsNeChk cells runs abPts = true) :
    Spike.Lib.X64AbOffL.RunsOff (_root_.Executable.labels exe).label runs := by
  intro r hr j hlo hhi
  have hne := runsNe_of_chk hp h r hr j hlo hhi
  have z : ∀ a : Int64, a + Int64.ofNat 0 = a := fun a => by
    rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq
  · exact hne ("scc_rt_abort_write_exit", 0) (by simp [abPts]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_abort_threads_exit", 0) (by simp [abPts]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_take_site", 0) (by simp [abPts]) (by simpa only [z] using heq)
  · exact hne ("scc_rt_release_site", 0) (by simp [abPts]) (by simpa only [z] using heq)

/-- **`X64WakeOff.RunsNe` decided on the listing**: the point `(l', k')`'s pc
is none of the runs'. -/
theorem runsNeQ_of_chk {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) {runs : List (Label × Nat × Nat)} {l : Label} {k : Nat}
    (h : runsNeChk cells runs [(l, k)] = true) :
    Spike.Lib.X64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat k) runs :=
  fun r hr j hlo hhi => runsNe_of_chk hp h r hr j hlo hhi (l, k) List.mem_cons_self

end Spike.Lib.X64.RunsOff

/-- info: 'Spike.Lib.X64.RunsOff.runsNe_of_chk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.RunsOff.runsNe_of_chk

/-- info: 'Spike.Lib.X64.RunsOff.runsOffA_of_chk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.RunsOff.runsOffA_of_chk

/-- info: 'Spike.Lib.X64.RunsOff.runsOff_of_chk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.RunsOff.runsOff_of_chk
