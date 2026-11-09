/-
**wake.w's worker store point on the target, x86-64** (the x64 twin of
`Spike/Lib/A64WakePass.lean`, `WCompat.pass`): the pcs past the worker's
release store (`wakePostRuns`, byte ranges after labels of the listing), the
fragment `wakePass` (the pc is one of them iff the source is past its store),
and `wakePass` at every node of the child's segments (`ThrZ`, the stub's
`NodeZ`), for `seg_childPreNN` at `Z := wakePass`.

Every node's invariant pins its control (`c = c'`), and every node's pc is a
label of the listing plus a byte offset; whether such a pc is past the store
is decided on the listing (`passChk`, `pcIn_iff`).

- `wakePostRuns`: `wc_worker`'s `.entry` from the instruction after its
  store (`wake_storeAt`) and its `.x14`, `scc_rt_unpark`,
  `scc_rt_thr_worker`'s `.x12` (past `wc_worker`'s return, to its exit);
  `wake_runsOk`.
- `wakePassT`: `PcIn wakePostRuns`, the flag record's `passT`.
- `WPassC c`: the source is past its store (`wkUnpark` or `ret ()`), the
  right side of `WCompat.pass`; `wakePass s c`: `PcIn wakePostRuns s ↔ WPassC c`.
- `nodeZ_pass`, `nodeZ_pass0`, `pro_pass`: a node (prologue) with a decided
  pc check.
- `head_pass`, `wk_pass`, `unpk_pass`, `tail_pass`: each function's nodes.
- `thrZ_pass`, `cZ_pass`: `wakePass` at every node of the thread worker's
  run and of the child's stub, given which controls are past the store.
- `kidC_not`, `wc1_not`, `wkC2_pass`, `wkC3_pass`: the child's controls;
  `childThrZ`: `seg_childPreNN`'s `ThrZ` premise at `Z := wakePass` (and
  `cZ_pass hp (kidC_not ..)` its `hZc`).

**Unlike AArch64** (forced by the x64 shape): the runs are byte ranges
(`Spike/Lib/X64PcRuns.lean`; AArch64: instruction counts, the pc
`label + 4k`), so `passChk` takes the list of a node's byte offsets (its
block's `cellOff`s; the prologue's `0 .. 35`); the release store is a plain
`movq` (TSO; AArch64: `stlr`), at `.Lwc_worker.entry + 11`; the stub is four
nodes (`testq`, `je` at `.Lwc_main.x3 + 48`, `+ 51`; `xorl`, the call at
the child's label, `+ 2`); `scc_rt_unpark`'s nodes (its `xchg`) and the
tail's are those of `X64WorkerRows`/`X64WakeWorker`.
-/
import Spike.Lib.X64PcRuns
import Spike.Lib.X64WakeChildNN
import Spike.Lib.WorkerSrc

namespace Spike.Lib.X64.Flow.Worker.Wake.Pass

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.PcRuns (PcIn runsOk inRuns labelPos cellsSize pcIn_iff)
open Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZ thrJ thrJE wcJE)
open Spike.Lib.X64.WakePh.WcClone (x21L)
open Spike.Lib.X64.WakePh.Child (cN childN childJ chL)
open Spike.Lib.X64.Flow.Worker.Wake.Child (kidC cBlk)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerTy workerRest wc1)
open Spike.Lib.WorkerSrc (wkUnpark)

set_option linter.unusedSimpArgs false

/-- **The pcs past the worker's release store**: `wc_worker`'s `.entry`
from byte 14 (past the store's 3 bytes at 11) and its `.x14`,
`scc_rt_unpark`, `scc_rt_thr_worker`'s `.x12` (each to its label's last
byte). -/
def wakePostRuns : List (Label × Nat × Nat) :=
  [(".Lwc_worker.entry", 14, 23), (".Lwc_worker.x0", 0, 5), ("scc_rt_unpark", 0, 12),
    (".Lscc_rt_unpark.entry", 0, 37), (".Lscc_rt_unpark.wake", 0, 73), (".Lscc_rt_unpark.done", 0, 5),
    (".Lscc_rt_thr_worker.x0", 0, 48)]

theorem wake_runsOk : runsOk SccCode.wakeCells wakePostRuns = true := by decide +kernel

/-- `wc_worker`'s `.entry`: the store (3 bytes) at byte 11, then the run of
`wakePostRuns` to the label's end at byte 23. -/
theorem wake_storeAt : Scc.Cert.Rt.X64.blockAt SccCode.wakeCells ".Lwc_worker.entry" 2 11
    ((stDir .rcx 0 .rax, 3) :: WkTailW.b1) = true := by decide +kernel

/-- **The target store point**: the pc is past the worker's store
(`WCompat.pass`'s `passT`). -/
def wakePassT (s : State) : Prop := PcIn wakePostRuns s

/-- **The source is past its store** (`WCompat.pass`'s right side). -/
def WPassC (c : Ctl) : Prop := c.term = wkUnpark ∨ c.term = .ret .unit

/-- **The target store point agrees with the source's**: the pc is past the
store iff the control is past the store. -/
def wakePass : Frag isa := fun s c => (wakePassT s ↔ WPassC c)

/-- **The bytes `xs` after `l` are all (`b`) or none (`!b`) past the store**,
decided on the listing. -/
def passChk (l : Label) (xs : List Nat) (b : Bool) : Bool :=
  xs.all fun x => (match labelPos SccCode.wakeCells l with
    | some p => decide (p + x < cellsSize SccCode.wakeCells)
    | none => false) && inRuns SccCode.wakeCells wakePostRuns l x == b

theorem wp_false {c : Ctl} (h : ¬ WPassC c) : WPassC c ↔ false = true := ⟨fun h' => absurd h' h, nofun⟩

theorem wp_true {c : Ctl} (h : WPassC c) : WPassC c ↔ true = true := ⟨fun _ => rfl, fun _ => h⟩

theorem kidC_not (T : Ty) (w1 w2 : TermRun.Word) : ¬ WPassC (kidC T w1 w2) := by
  simp [WPassC, kidC, wkUnpark]

theorem wc1_not (w1 w2 : TermRun.Word) : ¬ WPassC (wc1 workerTy w1 w2) := by
  simp [WPassC, wc1, workerRest, wkUnpark]

theorem wkC2_pass {env : TermRun.Env} : WPassC ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), env, none⟩ :=
  .inl rfl

theorem wkC3_pass {env : TermRun.Env} : WPassC ⟨.ret .unit, env, none⟩ := .inr rfl

/-- A node of no instructions keeps any fragment. -/
theorem nodeZ_nil {Z : Frag isa} {exe : _root_.Executable} {n : ND} : NodeZ Z exe n [] :=
  fun _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe SccCode.wakeCells kp)
include hp

/-- **`wakePass` at a decided pc**: the byte `x` after `l`. -/
theorem pass_at {l : Label} {xs : List Nat} {b : Bool} (hchk : passChk l xs b = true) {c : Ctl}
    (hb : WPassC c ↔ b = true) {s : State} {x : Nat} (hx : x ∈ xs) (he : s.exe = exe)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat x) :
    wakePass s c := by
  simp only [passChk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨hl, hall⟩ := hchk x hx
  split at hl
  next p hp' =>
    show wakePassT s ↔ WPassC c
    unfold wakePassT
    rw [pcIn_iff hp wake_runsOk he hp' (by simpa using hl) hs, hall]
    exact hb.symm
  next => cases hl

/-- **`wakePass` at a node** whose invariant pins the control to `c'`, at
`off` bytes after `l`. -/
theorem nodeZ_pass {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat} {b : Bool}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hchk : passChk l ((List.range blk.length).map fun k => off + cellOff blk k) b = true) {c' : Ctl}
    (hc : ∀ σ c, n.J σ c → c = c') (hb : WPassC c' ↔ b = true) :
    NodeZ wakePass exe n blk := by
  intro s σ c k hk he hs hJ
  obtain rfl := hc σ c hJ
  refine pass_at hp hchk hb (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩) he ?_
  rw [hs, hpc, Int64.add_assoc, ← Int64.ofNat_add]

/-- **`wakePass` at a node at a label.** -/
theorem nodeZ_pass0 {n : ND} {blk : List (Directive × Nat)} {l : Label} {b : Bool}
    (hpc : n.pc = (_root_.Executable.labels exe).label l)
    (hchk : passChk l ((List.range blk.length).map fun k => 0 + cellOff blk k) b = true) {c' : Ctl}
    (hc : ∀ σ c, n.J σ c → c = c') (hb : WPassC c' ↔ b = true) :
    NodeZ wakePass exe n blk :=
  nodeZ_pass hp (by rw [hpc]; exact (Int64.add_zero _).symm) hchk hc hb

/-- **`wakePass` at a prologue** (bytes `0 .. 35` after `fn`), before the
store. -/
theorem pro_pass {fn : Label} (hchk : passChk fn (List.range 36) false = true)
    {J : AS → Ctl → Prop} {c' : Ctl} (hc : ∀ σ c, J σ c → c = c') (h0 : ¬ WPassC c') :
    ∀ (s : State) σ c (k : Nat), k ≤ 35 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat k → J σ c → wakePass s c := by
  intro s σ c k hk he hs hJ
  obtain rfl := hc σ c hJ
  exact pass_at hp hchk (wp_false h0) (List.mem_range.2 (by omega)) he hs

/-- Closes `nodeZ_pass`'s side goals: the node's pc, the decided check, the
control's pin. -/
local macro "zn" : tactic =>
  `(tactic| first
    | (show passChk _ _ _ = true; decide +kernel)
    | (intro σ c h
       first | exact h.1 | exact h.1.1 | exact h)
    | rfl)

/-- `wakePass` at `scc_rt_thr_worker`'s head, before the store. -/
theorem head_pass {c0 c1 : Ctl} {A B tp sp0 : BitVec 64} (h0 : ¬ WPassC c0) (i : ThrHeadW.TN) :
    NodeZ wakePass exe (ThrHeadW.tN (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0)
      (fun _ c => c = c1) i) (ThrHeadW.blkN i) := by
  cases i
  · refine nodeZ_pass0 hp (l := ".Lscc_rt_thr_worker.entry") ?_ ?_ ?_ (wp_false h0) <;> zn
  · exact nodeZ_nil

/-- `wakePass` at `wc_worker`'s nodes: before the store at `c1`, past it at
`c2`, `c3`. -/
theorem wk_pass {c1 c2 c3 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (h1 : ¬ WPassC c1) (h2 : WPassC c2)
    (h3 : WPassC c3) (i : WkTailW.PN) :
    NodeZ wakePass exe (WkTailW.N (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp sp i)
      (WkTailW.blkN i) := by
  cases i
  · refine nodeZ_pass0 hp (l := ".Lwc_worker.entry") ?_ ?_ ?_ (wp_false h1) <;> zn
  · refine nodeZ_pass hp (l := ".Lwc_worker.entry") (off := 11) ?_ ?_ ?_ (wp_false h1) <;> zn
  · refine nodeZ_pass hp (l := ".Lwc_worker.entry") (off := 14) ?_ ?_ ?_ (wp_true h2) <;> zn
  · exact nodeZ_nil
  · refine nodeZ_pass0 hp (l := ".Lwc_worker.x0") ?_ ?_ ?_ (wp_true h3) <;> zn

/-- `wakePass` at `scc_rt_unpark`'s nodes, past the store. -/
theorem unpk_pass {c2 c3 : Ctl} {B rbp1 ra1 tp : BitVec 64} (h2 : WPassC c2) (h3 : WPassC c3)
    (i : Unpark.PN) :
    NodeZ wakePass exe (Unpark.N (_root_.Executable.labels exe).label c2 c3 B rbp1 ra1 tp i) (Unpark.blkN i) := by
  cases i
  · refine nodeZ_pass0 hp (l := "scc_rt_unpark") ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass0 hp (l := ".Lscc_rt_unpark.entry") ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_unpark.entry") (off := 11) ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_unpark.entry") (off := 15) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_unpark.entry") (off := 35) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass0 hp (l := ".Lscc_rt_unpark.wake") ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_unpark.wake") (off := 62) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_unpark.wake") (off := 64) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass0 hp (l := ".Lscc_rt_unpark.done") ?_ ?_ ?_ (wp_true h3) <;> zn

/-- `wakePass` at `scc_rt_thr_worker`'s tail, past the store. -/
theorem tail_pass {c3 : Ctl} {tp sp0 : BitVec 64} (h3 : WPassC c3) (i : ThrTailW.PN) :
    NodeZ wakePass exe (ThrTailW.N (_root_.Executable.labels exe).label c3 tp sp0 i) (ThrTailW.blkN i) := by
  cases i
  · refine nodeZ_pass0 hp (l := ".Lscc_rt_thr_worker.x0") ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_thr_worker.x0") (off := 9) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_thr_worker.x0") (off := 24) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_thr_worker.x0") (off := 28) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".Lscc_rt_thr_worker.x0") (off := 40) ?_ ?_ ?_ (wp_true h3) <;> zn

/-- **`wakePass` at every node of the thread worker's run**, its controls
before (`c0`, `c1`) and past (`c2`, `c3`) the store. -/
theorem thrZ_pass {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} (h0 : ¬ WPassC c0) (h1 : ¬ WPassC c1)
    (h2 : WPassC c2) (h3 : WPassC c3) : ThrZ wakePass exe c0 c1 c2 c3 A B tp sp0 where
  pro := pro_pass hp (fn := "scc_rt_thr_worker") (by decide +kernel) (fun _ _ h => h.1) h0
  head := head_pass hp h0
  wpro _ _ := pro_pass hp (fn := "wc_worker") (by decide +kernel) (fun _ _ h => h.1) h1
  wk _ _ _ := wk_pass hp h1 h2 h3
  unpk _ _ := unpk_pass hp h2 h3
  tail := tail_pass hp h3

/-- **`wakePass` at the child's stub**, before the store. -/
theorem cZ_pass {cW : Ctl} {A B tp sp0 : BitVec 64} (h0 : ¬ WPassC cW) :
    ∀ i, NodeZ wakePass exe (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  intro i
  cases i
  · refine nodeZ_pass hp (l := x21L) (off := 48) ?_ ?_ ?_ (wp_false h0) <;> zn
  · refine nodeZ_pass hp (l := x21L) (off := 51) ?_ ?_ ?_ (wp_false h0) <;> zn
  · refine nodeZ_pass0 hp (l := chL) ?_ ?_ ?_ (wp_false h0) <;> zn
  · refine nodeZ_pass hp (l := chL) (off := 2) ?_ ?_ ?_ (wp_false h0) <;> zn

/-- **`wakePass` at the spawned child's nodes** (`seg_childPreNN`'s `ThrZ`
premise at `Z := wakePass`): its controls after the tail call, the `split`,
the `store` and the `unpark`. -/
theorem childThrZ (T : Ty) (w1 w2 : TermRun.Word) (A B tp sp0 : BitVec 64) :
    ThrZ wakePass exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_pass hp (kidC_not T w1 w2) (wc1_not w1 w2) wkC2_pass wkC3_pass

end Inst

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Pass.childThrZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms childThrZ

end Spike.Lib.X64.Flow.Worker.Wake.Pass
