/-
**Off the `writeErr` and `threads` abort sites and the transfer sites, by
label: the definitions** (AArch64), light enough for the segment
files to import (`Spike/Lib/A64AbOffL.lean` relates them to the marks).

- `PcOff lab q`, `AbOffL lab`: the pc is none of `scc_rt_abort_write_exit`,
  `scc_rt_abort_threads_exit`, `scc_rt_take_site`, `scc_rt_release_site`
  (`WakeM0.MSide.off`, `WCompat0.noSite0`).
- `NotLdAt A s`: the state's instruction is no load at address `A` (the
  flag's, `WCompat0.flagLd`); `TlsW lab A c0`: `PcOff`, `NotLdAt A` and the
  source control `c0` (the thread-pointer load's `W`, `WaitLoop`'s `htls`).
- `RunsOff lab runs`: every pc `label l + 4j` of the runs is off them
  (`abOffL_of_runs`); a segment's `W` checks are this hypothesis, decided
  on the listing.
-/
import Spike.Lib.A64Flow

namespace Spike.Lib.A64AbOffL

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **A pc off the `writeErr` and `threads` exit calls and the two transfer
sites** (by label). -/
def PcOff (lab : String → Int64) (q : Int64) : Prop :=
  q ≠ lab "scc_rt_abort_write_exit" ∧ q ≠ lab "scc_rt_abort_threads_exit" ∧ q ≠ lab "scc_rt_take_site" ∧
    q ≠ lab "scc_rt_release_site"

/-- **The pc is off the `writeErr` and `threads` exit calls and the two
transfer sites** (by label). -/
def AbOffL (lab : String → Int64) : Frag isaLSE2 :=
  fun s _ => PcOff lab s.st.2

/-- **No load at `A`**: the state's instruction is no load whose location
is at address `A`. -/
def NotLdAt (A : BitVec 64) (s : State) : Prop :=
  ∀ kl (Lc : Loc) k, isaLSE2.exec s = some (.load kl false Lc k) → Lc.addr ≠ A

/-- **The thread-pointer load's states**: off the exits and the transfer
sites, no load at the flag's address `A`, the source at `c0`. -/
def TlsW (lab : String → Int64) (A : BitVec 64) (c0 : Ctl) : Frag isaLSE2 :=
  fun s c => PcOff lab s.st.2 ∧ NotLdAt A s ∧ c = c0

/-- A state whose instruction runs to `.done` loads nothing. -/
theorem notLdAt_of_done {A : BitVec 64} {s s' : State} (h : isaLSE2.exec s = some (.done s')) : NotLdAt A s :=
  fun _ _ _ h' => by rw [h] at h'; cases h'

/-- A state whose instruction faults loads nothing. -/
theorem notLdAt_of_fault {A : BitVec 64} {s : State} {m : String} (h : isaLSE2.exec s = some (.fault m)) :
    NotLdAt A s :=
  fun _ _ _ h' => by rw [h] at h'; cases h'

/-- **Every pc of the runs is off the two exit calls**: `label l + 4j` for a
run `(l, lo, hi)` and `lo ≤ j < hi` (the runs' format of
`Spike.Lib.A64.PcRuns`). -/
def RunsOff (lab : String → Int64) (runs : List (String × Nat × Nat)) : Prop :=
  ∀ q ∈ runs, ∀ j, q.2.1 ≤ j → j < q.2.2 → PcOff lab (lab q.1 + Int64.ofNat (4 * j))

/-- A state at a pc of the runs is `AbOffL`. -/
theorem abOffL_of_runs {lab : String → Int64} {runs : List (String × Nat × Nat)} (h : RunsOff lab runs)
    {l : String} {lo hi j : Nat} (hq : (l, lo, hi) ∈ runs) (hlo : lo ≤ j) (hhi : j < hi) {s : State} {c : Ctl}
    (hpc : s.st.2 = lab l + Int64.ofNat (4 * j)) : AbOffL lab s c := by
  show PcOff lab s.st.2
  rw [hpc]; exact h _ hq j hlo hhi

/-- `RunsOff` of a sublist. -/
theorem RunsOff.mono {lab : String → Int64} {runs runs' : List (String × Nat × Nat)} (h : RunsOff lab runs)
    (hs : ∀ q ∈ runs', q ∈ runs) : RunsOff lab runs' :=
  fun q hq => h q (hs q hq)

end Spike.Lib.A64AbOffL
