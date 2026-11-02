/-
**hello.w's worker segment's concrete control fact, x86-64** (`PassZ`, `ZStoreOk`; the twin of
`Spike/Lib/A64HelloZ.lean`, its node half): the fragment `ZH exe kp` the worker's frame-aware segment carries,
and its part `Z0` at every node of the worker's, the thread worker's and the child's segments, decided per pc on
hello.w's cells.

`ZH` is `Z0` and, on no frame, wake's `SysSafe` (no `write` at all), which the segment keeps from wake's `NN` leaves:
a node fact cannot see the registers, and the store phase's `syscall`s (`futex`, `exit`) are told from `print`'s
`write` only by `%rax`.

- `NotUnpk c`: the control at no `unpark` binding.
- `Z0 exe kp s c fs`: the store points agree (`Pass.helloPass`); on no frame off `scc_rt_abort_write`'s system
  calls (`AbW`); on a frame the control at no `unpark` binding; the pc not the program's end. `ZH`: with `SysSafe`
  on no frame.
- `abWRuns`, `abW_pcIn`, `offChk`, `off_at`: `AbW`'s pcs as runs, a decided check that a node's bytes are none of
  them; `endOff_at`, `endOff_pcIn`: a byte of the cells, of runs of the cells, is not their end.
- `node0F`, `node0T`, `nodeFr`, `pro0`: `Z0` at a node on no frame (before / past the store), on a frame, at a
  prologue's bytes.
- `wc_hz`, `wc_hZE`, `wc_hZC`, `wc_hZP`, `wc_hZA`, `wc_hZu`, `wc_hZW`, `wc_hZU`: the worker segment's premises at
  `Z := Z0 exe kp`; `thr_hz`, `thr_hZE`, `thr_hZT`, `child_hZc`: the thread worker's and the child's.

Unlike AArch64: a node's pcs are its block's byte offsets (`cellOff`; AArch64: `4k`), so the checks take byte
lists and the end is excluded by the bytes' positions (`endOff_at`, from `passChk`'s bound; AArch64: through the
run's cells); prologues are their bytes through `.entry`'s first (AArch64: 15 instructions at the stack check);
the tails are at their executing offsets (`HelloTail.NA`, `HThrTail.NA`); `print`'s nodes and the abort path are
stated with their invariant and runs left free (the consumer's `NotUnpk` facts, `Pass.off_of_pcIn`'s decided
hypotheses), as in `X64HelloPass`. The consumers' premises `passZ_ZH` and `zStoreOk_ZH` (over `HelloPassH`,
`HelloW1StoreZ`) are not stated here.
-/
import Spike.Lib.X64HelloPass
import Spike.Lib.X64HelloNN

namespace Spike.Lib.X64.Flow.Worker.Hello.Z

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.PcRuns (PcIn runsOk inRuns labelPos cellsSize pcIn_iff label_eq lays_size ofNat_inj)
open Spike.Lib.X64.Flow.Worker Spike.Lib.X64.Flow.Worker.Hello
open Spike.Lib.X64.Flow.Worker.Hello.Child (cN CN cBlk x25L chL)
open Spike.Lib.X64.Flow.Worker.Hello.Pass (helloPass helloPassT HPassC PB passChk pass_at pass_off pass_on
  nodeZ_nil hello_runsOk)
open SccCode (helloCells)

set_option linter.unusedSimpArgs false

/-- **The control at no `unpark` binding.** -/
def NotUnpk (c : Ctl) : Prop := ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e

/-- **The worker segment's pc and control facts**: the store points agree; on no frame off `scc_rt_abort_write`'s
system calls; on a frame at no `unpark` binding; off the program's end. -/
def Z0 (exe : _root_.Executable) (kp : Nat) : FragS isa := fun s c fs =>
  helloPass s c fs ∧ (fs = [] → ¬ AbW exe s) ∧ (fs ≠ [] → NotUnpk c) ∧ s.st.2 ≠ endOf exe helloCells kp

/-- **The worker segment's concrete control fact**: `Z0`, and on no frame no `write` (the segment's fragment). -/
def ZH (exe : _root_.Executable) (kp : Nat) : FragS isa := fun s c fs =>
  Z0 exe kp s c fs ∧ (fs = [] → SysSafe s)

/-- **`hZu` at `Z0`.** -/
theorem z0_unpk {exe : _root_.Executable} {kp : Nat} :
    ∀ (fr : TermRun.Frame) s c, Z0 exe kp s c [fr] → NotUnpk c :=
  fun _ _ _ h => h.2.2.1 (List.cons_ne_nil _ _)

/-! ## Runs of the cells -/

/-- **`scc_rt_abort_write`'s two system calls**: the `write` at `.entry + 34`, the `exit_group` at the exit
label. -/
def abWRuns : List (Label × Nat × Nat) :=
  [(".Lscc_rt_abort_write.entry", 34, 35), ("scc_rt_abort_write_exit", 0, 1)]

theorem abWRuns_ok : runsOk helloCells abWRuns = true := by decide +kernel

/-- `AbW` is a pc of `abWRuns`. -/
theorem abW_pcIn {exe : _root_.Executable} {s : State} (he : s.exe = exe) (h : AbW exe s) : PcIn abWRuns s := by
  rcases h with h | h
  · refine ⟨(".Lscc_rt_abort_write.entry", 34, 35), by simp [abWRuns], 34, Nat.le_refl _, by decide, ?_⟩
    rw [he, h]; rfl
  · refine ⟨("scc_rt_abort_write_exit", 0, 1), by simp [abWRuns], 0, Nat.le_refl _, by decide, ?_⟩
    rw [he, h]; exact (Int64.add_zero _).symm

/-- **None of the bytes `xs` after `l` is in `A`**, decided on the cells. -/
def offChk (A : List (Label × Nat × Nat)) (l : Label) (xs : List Nat) : Bool :=
  xs.all fun x => (match labelPos helloCells l with
    | some p => decide (p + x < cellsSize helloCells)
    | none => false) && !inRuns helloCells A l x

/-- The bytes of a node's block at `off`. -/
abbrev offs (off : Nat) (blk : List (Directive × Nat)) : List Nat :=
  (List.range blk.length).map fun k => off + cellOff blk k

theorem mem_offs {off : Nat} {blk : List (Directive × Nat)} {k : Nat} (hk : k < blk.length) :
    off + cellOff blk k ∈ offs off blk :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

section Inst

variable {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe helloCells kp)
include hp

/-- **Off `A` at a decided pc**: the byte `x` after `l`. -/
theorem off_at {A : List (Label × Nat × Nat)} (hok : runsOk helloCells A = true) {l : Label} {xs : List Nat}
    (hchk : offChk A l xs = true) {s : State} {x : Nat} (hx : x ∈ xs) (he : s.exe = exe)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat x) : ¬ PcIn A s := by
  simp only [offChk, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨hl, hall⟩ := hchk x hx
  split at hl
  next p hp' =>
    rw [pcIn_iff hp hok he hp' (by simpa using hl) hs, hall]
    exact Bool.false_ne_true
  next => cases hl

/-- **A byte of the cells is not their end**: `label l + x`, `x` within the cells' bytes after `l`. -/
theorem endOff_at {l : Label} {p x : Nat} (hl : labelPos helloCells l = some p) (hx : p + x < cellsSize helloCells)
    {q : Int64} (hs : q = (_root_.Executable.labels exe).label l + Int64.ofNat x) : q ≠ endOf exe helloCells kp := by
  have hS := lays_size hp
  rw [label_eq hp hl, Int64.add_assoc, ← Int64.ofNat_add] at hs
  intro heq
  rw [hs] at heq
  have := ofNat_inj (by omega) (by unfold Kraken.Executable.sizeBefore cellsSize at *; omega) heq
  unfold Kraken.Executable.sizeBefore cellsSize at *
  omega

/-- **A byte of decided bytes after `l`** is not the cells' end. -/
theorem endOff_chk {l : Label} {xs : List Nat} {b : Bool} (hchk : passChk l xs b = true) {x : Nat} (hx : x ∈ xs)
    {q : Int64} (hs : q = (_root_.Executable.labels exe).label l + Int64.ofNat x) : q ≠ endOf exe helloCells kp := by
  simp only [passChk, List.all_eq_true, Bool.and_eq_true] at hchk
  have hl := (hchk x hx).1
  split at hl
  next p hp' => exact endOff_at hp hp' (by simpa using hl) hs
  next => cases hl

/-- **A pc of runs of the cells is not their end.** -/
theorem endOff_pcIn {A : List (Label × Nat × Nat)} (hok : runsOk helloCells A = true) {s : State}
    (he : s.exe = exe) (h : PcIn A s) : s.st.2 ≠ endOf exe helloCells kp := by
  obtain ⟨q, hq, j, -, hj, hs⟩ := h
  simp only [runsOk, List.all_eq_true] at hok
  have hl := hok q hq
  split at hl
  next p hp' =>
    simp only [decide_eq_true_eq] at hl
    rw [he] at hs
    exact endOff_at hp hp' (by omega) hs
  next => cases hl

/-- **`Z0` at a node on no frame, before the store**: its pc decided, its controls not past the store. -/
theorem node0F {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hchk : passChk l (offs off blk) false = true) (hab : offChk abWRuns l (offs off blk) = true)
    (hb : ∀ σ c, n.J σ c → ¬ HPassC c) : NodeZ (fun s c => Z0 exe kp s c []) exe n blk := by
  intro s σ c k hk he hs hJ
  have hs' : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (off + cellOff blk k) := by
    rw [hs, hpc, Int64.add_assoc, ← Int64.ofNat_add]
  exact ⟨pass_off (pass_at hp hchk (mem_offs hk) he hs') fun _ => hb σ c hJ,
    fun _ h => off_at hp abWRuns_ok hab (mem_offs hk) he hs' (abW_pcIn he h), fun h => absurd rfl h,
    endOff_chk hp hchk (mem_offs hk) hs'⟩

/-- **`Z0` at a node on no frame, past the store.** -/
theorem node0T {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hchk : passChk l (offs off blk) true = true) (hab : offChk abWRuns l (offs off blk) = true)
    (hb : ∀ σ c, n.J σ c → HPassC c) : NodeZ (fun s c => Z0 exe kp s c []) exe n blk := by
  intro s σ c k hk he hs hJ
  have hs' : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (off + cellOff blk k) := by
    rw [hs, hpc, Int64.add_assoc, ← Int64.ofNat_add]
  exact ⟨pass_on (pass_at hp hchk (mem_offs hk) he hs') rfl (hb σ c hJ),
    fun _ h => off_at hp abWRuns_ok hab (mem_offs hk) he hs' (abW_pcIn he h), fun h => absurd rfl h,
    endOff_chk hp hchk (mem_offs hk) hs'⟩

/-- **`Z0` at a node on a frame** (before the store), its controls at no `unpark` binding. -/
theorem nodeFr {fr : TermRun.Frame} {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hchk : passChk l (offs off blk) false = true) (hu : ∀ σ c, n.J σ c → NotUnpk c) :
    NodeZ (fun s c => Z0 exe kp s c [fr]) exe n blk := by
  intro s σ c k hk he hs hJ
  have hs' : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (off + cellOff blk k) := by
    rw [hs, hpc, Int64.add_assoc, ← Int64.ofNat_add]
  exact ⟨pass_off (pass_at hp hchk (mem_offs hk) he hs') fun h => absurd h (List.cons_ne_nil _ _),
    fun h => absurd h (List.cons_ne_nil _ _), fun _ => hu σ c hJ, endOff_chk hp hchk (mem_offs hk) hs'⟩

/-- **`Z0` at a prologue**: its `n` bytes after `fn`, the control not past the store. -/
theorem pro0 {fn : Label} {n : Nat} (hchk : passChk fn (List.range n) false = true)
    (hab : offChk abWRuns fn (List.range n) = true) {J : AS → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    ∀ (s : State) σ c (k : Nat), k < n → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat k → J σ c → Z0 exe kp s c [] := by
  intro s σ c k hk he hs hJ
  have hk' := List.mem_range.2 hk
  exact ⟨pass_off (pass_at hp hchk hk' he hs) fun _ => hb σ c hJ,
    fun _ h => off_at hp abWRuns_ok hab hk' he hs (abW_pcIn he h), fun h => absurd rfl h,
    endOff_chk hp hchk hk' hs⟩

/-- Closes a node lemma's pc premise. -/
local macro "zpc" : tactic =>
  `(tactic| first | exact (Int64.add_zero _).symm | rfl)

/-- Closes a node lemma's decided check. -/
local macro "zk" : tactic => `(tactic| decide +kernel)

/-- Closes a node's control premise from the invariant's pinned control. -/
local macro "zp " h:term : tactic =>
  `(tactic| (intro σ c hJ; first
    | exact hJ ▸ $h | exact hJ.1 ▸ $h | exact hJ.1.1 ▸ $h | exact hJ.1.1.1 ▸ $h
    | (obtain ⟨_, _, h0, _⟩ := hJ; exact h0 ▸ $h)
    | (simp only [Unpark.N, Unpark.JE, Unpark.JI, Unpark.JS, HelloTail.NA, HelloTail.N, HelloTail.JI,
        HThrTail.NA, HThrTail.N, cN, childN, childJ] at hJ
       first
         | (subst hJ; exact $h) | (obtain ⟨rfl, -⟩ := hJ; exact $h) | (obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact $h)
         | exact hJ.1 ▸ $h | exact hJ.1.1 ▸ $h | exact hJ.2.1 ▸ $h)))

/-! ## The worker segment's premises -/

/-- **`wc_worker`'s prologue** (`hz`): its bytes up to and including `.entry`'s first, the control not past the
store. -/
theorem wc_hz {J : AS → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    ∀ (s : State) σ c (k : Nat), k < 56 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label "wc_worker" + Int64.ofNat k → J σ c → Z0 exe kp s c [] :=
  pro0 hp (by decide +kernel) (by decide +kernel) hb

/-- **`wc_worker`'s `.entry` nodes** (`hZE`), the controls not past the store. -/
theorem wc_hZE {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE1 ∧
      NodeZ (fun s c => Z0 exe kp s c []) exe (Body.wN (_root_.Executable.labels exe).label J Pr .mul)
        [(Body.wkMul.toDir, 4)] ∧
      NodeZ (fun s c => Z0 exe kp s c []) exe (Body.wN (_root_.Executable.labels exe).label J Pr .e2) Body.wkE2 :=
  ⟨node0F hp (l := ".Lwc_worker.entry") (off := 0) (by zpc) (by zk) (by zk) hb,
    node0F hp (l := ".Lwc_worker.entry") (off := 36) (by zpc) (by zk) (by zk)
      fun σ c ⟨_, hJ, _⟩ => hb _ c hJ,
    node0F hp (l := ".Lwc_worker.entry") (off := 40) (by zpc) (by zk) (by zk)
      fun σ c ⟨_, _, hJ, _⟩ => hb _ c hJ⟩

/-- **`wc_worker`'s call node** (`hZC`), the call's controls not past the store. -/
theorem wc_hZC {J Kc : AS → Ctl → Prop} (hK : ∀ σ c, Kc σ c → ¬ HPassC c) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (Body.wCall (_root_.Executable.labels exe).label J Kc)
      Spike.Lib.X64.Print.x0 :=
  node0F hp (l := "scc_rt_print") (off := 0) (by zpc) (by zk) (by zk) fun σ c h => hK σ c h.2

set_option maxHeartbeats 1600000 in
/-- **`print`'s nodes** (`hZP`), at a node with `Print.N`'s pc and offsets and any invariant `J` whose controls
are at no `unpark` binding. -/
theorem wc_hZP {fr : TermRun.Frame} {c0 : Ctl} {rbp0 ra : BitVec 64} {J : AS → Ctl → Prop}
    (hu : ∀ σ c, J σ c → NotUnpk c) (i : Print.PN) :
    NodeZ (fun s c => Z0 exe kp s c [fr]) exe
      ⟨(Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).pc,
        (Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).o, J⟩ (PrintF.FA.blkN i) := by
  cases i
  · exact nodeFr hp (l := "scc_rt_print") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.entry") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.loop") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.loop") (off := 20) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.write") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.write") (off := 20) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.write") (off := 22) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.write") (off := 42) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.chk2") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.chk2") (off := 16) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.chk3") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.chk3") (off := 16) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.adv") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.fail") (off := 0) (by zpc) (by zk) hu
  · exact nodeFr hp (l := ".Lscc_rt_print.done") (off := 0) (by zpc) (by zk) hu

/-- **The abort path** (`hZA`): on a frame at a pc of runs `A` of the cells none of whose bytes is past the store,
the abort's controls at no `unpark` binding. -/
theorem wc_hZA {A : List (Label × Nat × Nat)} (hok : runsOk helloCells A = true)
    (hdis : A.all (fun q => (List.range q.2.2).all fun j => !inRuns helloCells Pass.helloPostRuns q.1 j) = true)
    {fr : TermRun.Frame} {c' : Ctl} (hu : NotUnpk c') {s : State} (he : s.exe = exe) (h : PcIn A s) :
    Z0 exe kp s c' [fr] :=
  ⟨pass_off ⟨fun hs => absurd hs (Pass.off_of_pcIn hp hok hdis he h), nofun⟩
      fun h => absurd h (List.cons_ne_nil _ _),
    fun h => absurd h (List.cons_ne_nil _ _), fun _ => hu, endOff_pcIn hp hok he h⟩

omit hv hp in
/-- **On a frame no `unpark` binding** (`hZu`). -/
theorem wc_hZu : ∀ (fr : TermRun.Frame) s c, Z0 exe kp s c [fr] → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e :=
  fun _ _ _ h => h.2.2.1 (List.cons_ne_nil _ _)

/-- **`wc_worker`'s tail** (`hZW`), at its executing offsets: before the store at `cw`, past it at `c1`, `c2`. -/
theorem wc_hZW {cw c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (hw : ¬ HPassC cw) (h1 : HPassC c1)
    (h2 : HPassC c2) (i : HelloTail.PN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe
      (HelloTail.NA (_root_.Executable.labels exe).label cw c1 c2 A B rbp0 ra tp sp i) (HelloTail.blkN i) := by
  cases i
  · exact node0F hp (l := ".Lwc_worker.x17") (off := 0) (by zpc) (by zk) (by zk) (by zp hw)
  · exact node0F hp (l := ".Lwc_worker.x17") (off := 11) (by zpc) (by zk) (by zk) (by zp hw)
  · exact node0T hp (l := ".Lwc_worker.x17") (off := 14) (by zpc) (by zk) (by zk) (by zp h1)
  · exact nodeZ_nil
  · exact node0T hp (l := ".Lwc_worker.x18") (off := 0) (by zpc) (by zk) (by zk) (by zp h2)

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_unpark`'s nodes** (`hZU`), past the store. -/
theorem wc_hZU {c1 c2 : Ctl} {B rbp1 ra1 tp : BitVec 64} (h1 : HPassC c1) (h2 : HPassC c2) (i : Unpark.PN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
      (Unpark.blkN i) := by
  cases i
  · exact node0T hp (l := "scc_rt_unpark") (off := 0) (by zpc) (by zk) (by zk) (by zp h1)
  · exact node0T hp (l := ".Lscc_rt_unpark.entry") (off := 0) (by zpc) (by zk) (by zk) (by zp h1)
  · exact node0T hp (l := ".Lscc_rt_unpark.entry") (off := 11) (by zpc) (by zk) (by zk) (by zp h1)
  · exact node0T hp (l := ".Lscc_rt_unpark.entry") (off := 15) (by zpc) (by zk) (by zk) (by zp h2)
  · exact node0T hp (l := ".Lscc_rt_unpark.entry") (off := 35) (by zpc) (by zk) (by zk) (by zp h2)
  · exact node0T hp (l := ".Lscc_rt_unpark.wake") (off := 0) (by zpc) (by zk) (by zk) (by zp h2)
  · exact node0T hp (l := ".Lscc_rt_unpark.wake") (off := 62) (by zpc) (by zk) (by zk) (by zp h2)
  · exact node0T hp (l := ".Lscc_rt_unpark.wake") (off := 64) (by zpc) (by zk) (by zk) (by zp h2)
  · exact node0T hp (l := ".Lscc_rt_unpark.done") (off := 0) (by zpc) (by zk) (by zk) (by zp h2)

/-! ## The thread worker's and the child's premises -/

/-- **`scc_rt_thr_worker`'s prologue** (`hz`): its bytes up to and including `.entry`'s first. -/
theorem thr_hz {J : AS → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    ∀ (s : State) σ c (k : Nat), k < 52 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label "scc_rt_thr_worker" + Int64.ofNat k → J σ c →
      Z0 exe kp s c [] :=
  pro0 hp (by decide +kernel) (by decide +kernel) hb

/-- **`scc_rt_thr_worker`'s head** (`hZE`). -/
theorem thr_hZE {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (HThrHead.tN (_root_.Executable.labels exe).label J L .e)
      (HThrHead.blkN .e) :=
  node0F hp (l := ".Lscc_rt_thr_worker.entry") (off := 0) (by zpc) (by zk) (by zk) hb

/-- **`scc_rt_thr_worker`'s tail** (`hZT`), at its executing offsets, past the store. -/
theorem thr_hZT {c3 : Ctl} {tp sp0 : BitVec 64} (h3 : HPassC c3) (i : HThrTail.PN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 i)
      (HThrTail.blkN i) := by
  cases i
  · exact node0T hp (l := ".Lscc_rt_thr_worker.x13") (off := 0) (by zpc) (by zk) (by zk) (by zp h3)
  · exact node0T hp (l := ".Lscc_rt_thr_worker.x13") (off := 9) (by zpc) (by zk) (by zk) (by zp h3)
  · exact node0T hp (l := ".Lscc_rt_thr_worker.x13") (off := 24) (by zpc) (by zk) (by zk) (by zp h3)
  · exact node0T hp (l := ".Lscc_rt_thr_worker.x13") (off := 28) (by zpc) (by zk) (by zk) (by zp h3)
  · exact node0T hp (l := ".Lscc_rt_thr_worker.x13") (off := 40) (by zpc) (by zk) (by zk) (by zp h3)

/-- **The child's stub** (`hZc`), before the store. -/
theorem child_hZc {cW : Ctl} {w : Child.Words} {tp sp0 : BitVec 64} (h0 : ¬ HPassC cW) (i : CN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (cN (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i) := by
  cases i
  · exact node0F hp (l := x25L) (off := 96) (by zpc) (by zk) (by zk) (by zp h0)
  · exact node0F hp (l := x25L) (off := 99) (by zpc) (by zk) (by zk) (by zp h0)
  · exact node0F hp (l := chL) (off := 0) (by zpc) (by zk) (by zk) (by zp h0)
  · exact node0F hp (l := chL) (off := 2) (by zpc) (by zk) (by zk) (by zp h0)

end Inst

/-- `Z0` is inhabited: on a frame, off the store, at a control at no `unpark` binding, off the end. -/
example (exe : _root_.Executable) (kp : Nat) (s : State) (h : ¬ helloPassT s)
    (hend : s.st.2 ≠ endOf exe helloCells kp) (fr : TermRun.Frame) :
    Z0 exe kp s ⟨.ret .unit, [], none⟩ [fr] :=
  ⟨⟨fun h' => absurd h' h, fun ⟨h1, _⟩ => absurd h1 (List.cons_ne_nil _ _)⟩,
    fun h => absurd h (List.cons_ne_nil _ _), fun _ _ _ _ h => (by cases h), hend⟩

end Spike.Lib.X64.Flow.Worker.Hello.Z

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Z.wc_hZP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Z.wc_hZP
