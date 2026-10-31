/-
**Off every abort exit and the transfer sites, by label: wake's main**
(x86-64). The x64 twin of `Spike/Lib/A64WakeOffDef.lean`: the
wake-only strengthening of `Spike/Lib/X64AbOffLDef.lean`'s `PcOff` (which
hello1 keeps): main's rows after the spawn accept an `exit_group` at any
abort stub, so `post_abort` needs main off all five abort exits, not only
`writeErr`'s and `threads`'.

- `PcOffA lab q`, `AbOffA lab`: the pc is none of the five
  `scc_rt_abort_<kind>_exit` labels nor `scc_rt_take_site`,
  `scc_rt_release_site`; `pcOff_of_pcOffA`: it is `PcOff`.
- `TlsA lab A c0`: `PcOffA`, `NotLdAt A` and the source control `c0` (the
  thread-pointer load's `W`, `WaitLoop`'s `htls`).
- `RunsOffA lab runs`: every pc `label l + j` of the byte runs is `PcOffA`
  (decided on the listing, `X64RunsOff`); `pcOffA_add`, `pcOffA_at`: a pc
  of a run.
- `RunsNe lab q runs`: no pc of the byte runs is `q` (main's flag check `q`
  off its other post-spawn pcs); `runsNe_add`.

**Byte runs**, as `X64AbOffLDef`'s: a run `(l, lo, hi)` is the byte range
`[lo, hi)` after `label l` (AArch64: the instruction indices `j`, at
`label l + 4j`).
-/
import Spike.Lib.X64AbOffLDef

namespace Spike.Lib.X64WakeOff

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64AbOffL (PcOff NotLdAt)

/-- **A pc off every abort exit call and the two transfer sites** (by
label). -/
def PcOffA (lab : String → Int64) (q : Int64) : Prop :=
  q ≠ lab "scc_rt_abort_overflow_exit" ∧ q ≠ lab "scc_rt_abort_heap_exit" ∧
    q ≠ lab "scc_rt_abort_stack_exit" ∧ q ≠ lab "scc_rt_abort_write_exit" ∧
    q ≠ lab "scc_rt_abort_threads_exit" ∧ q ≠ lab "scc_rt_take_site" ∧ q ≠ lab "scc_rt_release_site"

/-- **The pc is off every abort exit call and the two transfer sites.** -/
def AbOffA (lab : String → Int64) : Frag isa :=
  fun s _ => PcOffA lab s.st.2

/-- **The thread-pointer load's states**: off every abort exit and the
transfer sites, no load at the flag's address `A`, the source at `c0`. -/
def TlsA (lab : String → Int64) (A : BitVec 64) (c0 : Ctl) : Frag isa :=
  fun s c => PcOffA lab s.st.2 ∧ NotLdAt A s ∧ c = c0

/-- `PcOffA` is `PcOff`. -/
theorem pcOff_of_pcOffA {lab : String → Int64} {q : Int64} (h : PcOffA lab q) : PcOff lab q :=
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **Every pc of the byte runs is off every abort exit and the transfer
sites**: `label l + j` for a run `(l, lo, hi)` and `lo ≤ j < hi`. -/
def RunsOffA (lab : String → Int64) (runs : List (String × Nat × Nat)) : Prop :=
  ∀ q ∈ runs, ∀ j, q.2.1 ≤ j → j < q.2.2 → PcOffA lab (lab q.1 + Int64.ofNat j)

/-- `RunsOffA` of a sublist. -/
theorem RunsOffA.mono {lab : String → Int64} {runs runs' : List (String × Nat × Nat)} (h : RunsOffA lab runs)
    (hs : ∀ q ∈ runs', q ∈ runs) : RunsOffA lab runs' :=
  fun q hq => h q (hs q hq)

/-- `RunsOffA` of an append. -/
theorem runsOffA_append {lab : String → Int64} {a b : List (String × Nat × Nat)} (ha : RunsOffA lab a)
    (hb : RunsOffA lab b) : RunsOffA lab (a ++ b) := fun q hq =>
  (List.mem_append.mp hq).elim (ha q) (hb q)

/-- `RunsOffA` is `X64AbOffL.RunsOff`. -/
theorem RunsOffA.runsOff {lab : String → Int64} {runs : List (String × Nat × Nat)} (h : RunsOffA lab runs) :
    Spike.Lib.X64AbOffL.RunsOff lab runs :=
  fun q hq j h1 h2 => pcOff_of_pcOffA (h q hq j h1 h2)

/-- **A pc of a run is off**: `q = label l + c`, and `c + k` within the byte
run `(l, lo, hi)`. -/
theorem pcOffA_add {lab : String → Int64} {runs : List (String × Nat × Nat)}
    (h : RunsOffA lab runs) {l : String} {lo hi c k : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c)
    (h2 : c + k < hi) {q : Int64} (hq' : q = lab l + Int64.ofNat c) :
    PcOffA lab (q + Int64.ofNat k) := by
  subst hq'
  rw [Int64.add_assoc, ← Int64.ofNat_add]
  exact h _ hq (c + k) (show lo ≤ c + k by omega) h2

/-- **A pc of a run is off** (`k = 0` form of `pcOffA_add`). -/
theorem pcOffA_at {lab : String → Int64} {runs : List (String × Nat × Nat)}
    (h : RunsOffA lab runs) {l : String} {lo hi c : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c)
    (h2 : c < hi) {q : Int64} (hq' : q = lab l + Int64.ofNat c) : PcOffA lab q := by
  subst hq'
  exact h _ hq c h1 h2

/-- **No pc of the byte runs is `q`**: `label l + j` for a run `(l, lo, hi)`
and `lo ≤ j < hi` (main's flag check `q` off its other post-spawn pcs). -/
def RunsNe (lab : String → Int64) (q : Int64) (runs : List (String × Nat × Nat)) : Prop :=
  ∀ r ∈ runs, ∀ j, r.2.1 ≤ j → j < r.2.2 → lab r.1 + Int64.ofNat j ≠ q

/-- **A pc of a run is not `q`**: `p = label l + c`, and `c + k` within the
byte run `(l, lo, hi)`. -/
theorem runsNe_add {lab : String → Int64} {q : Int64} {runs : List (String × Nat × Nat)}
    (h : RunsNe lab q runs) {l : String} {lo hi c k : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c)
    (h2 : c + k < hi) {p : Int64} (hp : p = lab l + Int64.ofNat c) : p + Int64.ofNat k ≠ q := by
  subst hp
  rw [Int64.add_assoc, ← Int64.ofNat_add]
  exact h _ hq (c + k) (show lo ≤ c + k by omega) h2

end Spike.Lib.X64WakeOff
