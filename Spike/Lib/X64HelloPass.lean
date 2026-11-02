/-
**hello.w's worker store point on the target, x86-64** (`PassZ`; the twin of
`Spike/Lib/A64HelloPass.lean`): the restatement of `X64WakePass.lean` at hello.w's listing (`SccCode.helloCells`,
`Spike/Lib/X64HelloCode.lean`). The pcs past the worker's release store (`helloPostRuns`, byte ranges after labels),
the frame-aware fragment `helloPass` (the pc is one of them iff the source is past its store on the empty stack),
and the side of the store each node of the worker's segments is on (`PB b`), decided per node on the listing.

- `helloPostRuns`: `wc_worker`'s `.x17` from byte 14 (past the store's 3 bytes at 11, `hello_storeAt`), its `.x18`,
  `scc_rt_unpark`, `scc_rt_thr_worker`'s `.x13`; `hello_runsOk`.
- `helloPassT`: `PcIn helloPostRuns`; `HPassC c`: the source is past its store (`wkUnpark` or `ret ()`);
  `helloPass s c fs`: `helloPassT s ↔ fs = [] ∧ HPassC c`; `PB b`: the pc is past the store iff `b`.
- `pass_of_b`, `pass_off`, `pass_on`: `helloPass` from a side and the control's.
- `passChk`, `pass_at`, `nodeZ_b`: a node's side, decided on the listing; `pro_off`, `off_of_pcIn`: a prologue's
  bytes, a set of runs, before the store.
- `tail_b`, `unpk_b`, `thrT_b`, `thrH_b`, `thrPro_off`, `wcPro_off`, `wE_b`, `wC_b`, `print_b`, `child_b`: the nodes
  of `wc_worker`'s tail (at their executing offsets, `HelloTail.NA`), `scc_rt_unpark`, the thread worker's tail
  (`HThrTail.NA`) and head, the prologues, `wc_worker`'s `.entry` and call, `print`, the child's stub.

Unlike AArch64 (forced by the x64 shape): the runs are byte ranges (`Spike/Lib/X64PcRuns.lean`; AArch64:
instruction counts, the pc `label + 4k`), so `passChk` takes the list of a node's byte offsets (its block's
`cellOff`s) and a prologue's check is over its bytes up to the function's `.entry` (`wc_worker`: 55,
`scc_rt_thr_worker`: 51; AArch64: 15 instructions); the release store is a plain `movq` (TSO; AArch64: `stlr`), at
`.Lwc_worker.x17 + 11`; labels carry no numbering prefix; `print`'s nodes are stated by `Print.N`'s pc and offsets
with any invariant (as `X64HelloRelZP`); and the abort path's runs are left to their module (`off_of_pcIn` at any
runs disjoint from the store's; AArch64: `abort_off` here).
-/
import Spike.Lib.X64PcRuns
import Spike.Lib.X64HelloWorkerTCS
import Spike.Lib.X64HelloWorker
import Spike.Lib.X64HelloWorkerLabels
import Spike.Lib.X64HelloWkTailNN
import Spike.Lib.X64HelloChildNN
import Spike.Lib.X64HelloPrintNN
import Spike.Lib.WorkerSrc
import Spike.Lib.SegS

namespace Spike.Lib.X64.Flow.Worker.Hello.Pass

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.PcRuns (PcIn runsOk inRuns labelPos cellsSize pcIn_iff)
open Spike.Lib.X64.Flow.Worker Spike.Lib.X64.Flow.Worker.Hello
open Spike.Lib.X64.Flow.Worker.Hello.Child (cN CN cBlk x25L chL)
open Spike.Lib.WorkerSrc (wkUnpark)

set_option linter.unusedSimpArgs false

/-- **The pcs past the worker's release store**: `wc_worker`'s `.x17` from byte 14 (past the store's 3 bytes at
11) and its `.x18`, `scc_rt_unpark`, `scc_rt_thr_worker`'s `.x13` (each to its label's last byte). -/
def helloPostRuns : List (Label × Nat × Nat) :=
  [(".Lwc_worker.x17", 14, 23), (".Lwc_worker.x18", 0, 5), ("scc_rt_unpark", 0, 12),
    (".Lscc_rt_unpark.entry", 0, 37), (".Lscc_rt_unpark.wake", 0, 73), (".Lscc_rt_unpark.done", 0, 5),
    (".Lscc_rt_thr_worker.x13", 0, 48)]

theorem hello_runsOk : runsOk SccCode.helloCells helloPostRuns = true := by decide +kernel

/-- `wc_worker`'s `.x17`: the store (3 bytes) at byte 11, then the run of `helloPostRuns` to the label's end at
byte 23. -/
theorem hello_storeAt : Scc.Cert.Rt.X64.blockAt SccCode.helloCells ".Lwc_worker.x17" 2 11
    ((stDir .rcx 0 .rax, 3) :: HelloTail.b1) = true := by decide +kernel

/-- **The target store point**: the pc is past the worker's store (`PassZ`'s `passT`). -/
def helloPassT (s : State) : Prop := PcIn helloPostRuns s

/-- **The source is past its store**: at `wkUnpark` or `ret ()`. -/
def HPassC (c : Ctl) : Prop := c.term = wkUnpark ∨ c.term = .ret .unit

/-- **The target store point agrees with the source's** on the frames (`PassZ`'s body at `helloPassT`). -/
def helloPass : FragS isa := fun s c fs => (helloPassT s ↔ fs = [] ∧ HPassC c)

/-- **The pc is past the store iff `b`.** -/
def PB (b : Bool) : Frag isa := fun s _ => (helloPassT s ↔ b = true)

/-- **The bytes `xs` after `l` are all (`b`) or none (`!b`) past the store**, decided on the listing. -/
def passChk (l : Label) (xs : List Nat) (b : Bool) : Bool :=
  xs.all fun x => (match labelPos SccCode.helloCells l with
    | some p => decide (p + x < cellsSize SccCode.helloCells)
    | none => false) && inRuns SccCode.helloCells helloPostRuns l x == b

/-- A node of no instructions keeps any fragment. -/
theorem nodeZ_nil {Z : Frag isa} {exe : _root_.Executable} {n : ND} : NodeZ Z exe n [] :=
  fun _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-! ## `helloPass` from the pc's side and the control's -/

/-- **`helloPass` from a side `b`** and the source's store point agreeing with it. -/
theorem pass_of_b {s : State} {c : Ctl} {fs : List TermRun.Frame} {b : Bool} (h : PB b s c)
    (hb : fs = [] ∧ HPassC c ↔ b = true) : helloPass s c fs :=
  h.trans hb.symm

/-- **Before the store on both sides**: the pc not past it, the source not past it on the empty stack. -/
theorem pass_off {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PB false s c)
    (hc : fs = [] → ¬ HPassC c) : helloPass s c fs :=
  pass_of_b h ⟨fun ⟨h1, h2⟩ => absurd h2 (hc h1), nofun⟩

/-- **Past the store on both sides.** -/
theorem pass_on {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PB true s c) (hfs : fs = [])
    (hc : HPassC c) : helloPass s c fs :=
  pass_of_b h ⟨fun _ => rfl, fun _ => ⟨hfs, hc⟩⟩

theorem hPassC_unpark {env : TermRun.Env} {h : Option _} : HPassC ⟨wkUnpark, env, h⟩ := .inl rfl

theorem hPassC_ret {env : TermRun.Env} {h : Option _} : HPassC ⟨.ret .unit, env, h⟩ := .inr rfl

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp)
include hp

/-- **The store point at a decided pc**: the byte `x` after `l`. -/
theorem pass_at {l : Label} {xs : List Nat} {b : Bool} (hchk : passChk l xs b = true) {s : State} {x : Nat}
    (hx : x ∈ xs) (he : s.exe = exe) (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat x) :
    helloPassT s ↔ b = true := by
  simp only [passChk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨hl, hall⟩ := hchk x hx
  split at hl
  next p hp' =>
    unfold helloPassT
    rw [pcIn_iff hp hello_runsOk he hp' (by simpa using hl) hs, hall]
  next => cases hl

/-- **The side of the store at a node** at `off` bytes after `l`, decided on the listing. -/
theorem nodeZ_b {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat} {b : Bool}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hchk : passChk l ((List.range blk.length).map fun k => off + cellOff blk k) b = true) :
    NodeZ (PB b) exe n blk := by
  intro s σ c k hk he hs _
  refine pass_at hp hchk (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩) he ?_
  rw [hs, hpc, Int64.add_assoc, ← Int64.ofNat_add]

/-- **A prologue is before the store**: its `n` bytes after `fn`, decided on the listing. -/
theorem pro_off {fn : Label} {n : Nat} (hchk : passChk fn (List.range n) false = true) :
    ∀ (s : State) (k : Nat), k < n → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat k → ¬ helloPassT s := by
  intro s k hk he hs h
  exact Bool.false_ne_true ((pass_at hp hchk (List.mem_range.2 hk) he hs).mp h)

/-- **Before the store on a set of runs** none of whose bytes is past it, decided on the listing. -/
theorem off_of_pcIn {A : List (Label × Nat × Nat)} (hok : runsOk SccCode.helloCells A = true)
    (hdis : A.all (fun q => (List.range q.2.2).all fun j => !inRuns SccCode.helloCells helloPostRuns q.1 j) = true)
    {s : State} (he : s.exe = exe) (h : PcIn A s) : ¬ helloPassT s := by
  obtain ⟨q, hq, j, -, hj, hs⟩ := h
  simp only [runsOk, List.all_eq_true] at hok
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hdis
  have hl := hok q hq
  split at hl
  next p hp' =>
    rw [he] at hs
    unfold helloPassT
    rw [pcIn_iff hp hello_runsOk he hp' (by simp only [decide_eq_true_eq] at hl; omega) hs, hdis q hq j hj]
    exact Bool.false_ne_true
  next => cases hl

/-- Closes `nodeZ_b`'s side goals: the node's pc, the decided check. -/
local macro "zb" : tactic =>
  `(tactic| first
    | (show passChk _ _ _ = true; decide +kernel)
    | rfl
    | exact (Int64.add_zero _).symm)

/-- Which of `wc_worker`'s tail nodes are past the store: from the one after the store. -/
def tailB : HelloTail.PN → Bool
  | .e => false | .st => false | .n3 => true | .unpk => true | .x18 => true

/-- **The store point at `wc_worker`'s tail nodes**, at their executing offsets (`seg_wcWorkerS`'s `hZW`). -/
theorem tail_b {c0 c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (i : HelloTail.PN) :
    NodeZ (PB (tailB i)) exe (HelloTail.NA (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp i)
      (HelloTail.blkN i) := by
  cases i
  · exact nodeZ_b hp (l := ".Lwc_worker.x17") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lwc_worker.x17") (off := 11) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lwc_worker.x17") (off := 14) (by zb) (by zb)
  · exact nodeZ_nil
  · exact nodeZ_b hp (l := ".Lwc_worker.x18") (off := 0) (by zb) (by zb)

/-- **`scc_rt_unpark`'s nodes are past the store** (`hZU`). -/
theorem unpk_b {c1 c2 : Ctl} {B rbp1 ra1 tp : BitVec 64} (i : Unpark.PN) :
    NodeZ (PB true) exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i) (Unpark.blkN i) := by
  cases i
  · exact nodeZ_b hp (l := "scc_rt_unpark") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.entry") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.entry") (off := 11) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.entry") (off := 15) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.entry") (off := 35) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.wake") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.wake") (off := 62) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.wake") (off := 64) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_unpark.done") (off := 0) (by zb) (by zb)

/-- **`scc_rt_thr_worker`'s tail is past the store**, at its executing offsets (`seg_thrWorkerH`'s `hZT`). -/
theorem thrT_b {c3 : Ctl} {tp sp0 : BitVec 64} (i : HThrTail.PN) :
    NodeZ (PB true) exe (HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 i) (HThrTail.blkN i) := by
  cases i
  · exact nodeZ_b hp (l := ".Lscc_rt_thr_worker.x13") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_thr_worker.x13") (off := 9) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_thr_worker.x13") (off := 24) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_thr_worker.x13") (off := 28) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_thr_worker.x13") (off := 40) (by zb) (by zb)

/-- **`scc_rt_thr_worker`'s head is before the store** (`hZE`). -/
theorem thrH_b {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : HThrHead.TN) :
    NodeZ (PB false) exe (HThrHead.tN (_root_.Executable.labels exe).label J L i) (HThrHead.blkN i) := by
  cases i
  · exact nodeZ_b hp (l := ".Lscc_rt_thr_worker.entry") (off := 0) (by zb) (by zb)
  · exact nodeZ_nil

/-- **`scc_rt_thr_worker`'s prologue is before the store** (`hz`): its bytes up to `.entry`. -/
theorem thrPro_off : ∀ (s : State) (k : Nat), k < 51 → s.exe = exe →
    s.st.2 = (_root_.Executable.labels exe).label "scc_rt_thr_worker" + Int64.ofNat k → ¬ helloPassT s :=
  pro_off hp (by decide +kernel)

/-- **`wc_worker`'s prologue is before the store** (`seg_wcWorkerS`'s `hz`): its bytes up to `.entry`. -/
theorem wcPro_off : ∀ (s : State) (k : Nat), k < 55 → s.exe = exe →
    s.st.2 = (_root_.Executable.labels exe).label "wc_worker" + Int64.ofNat k → ¬ helloPassT s :=
  pro_off hp (by decide +kernel)

/-- **`wc_worker`'s `.entry` nodes are before the store** (`hZE`): the block up to the multiply, the multiply,
the block after it. -/
theorem wE_b {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} :
    NodeZ (PB false) exe (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE1 ∧
      NodeZ (PB false) exe (Body.wN (_root_.Executable.labels exe).label J Pr .mul) [(Body.wkMul.toDir, 4)] ∧
      NodeZ (PB false) exe (Body.wN (_root_.Executable.labels exe).label J Pr .e2) Body.wkE2 :=
  ⟨nodeZ_b hp (l := ".Lwc_worker.entry") (off := 0) (by zb) (by zb),
    nodeZ_b hp (l := ".Lwc_worker.entry") (off := 36) (by zb) (by zb),
    nodeZ_b hp (l := ".Lwc_worker.entry") (off := 40) (by zb) (by zb)⟩

/-- **`wc_worker`'s call node is before the store** (`hZC`): `scc_rt_print`'s first block. -/
theorem wC_b {J Kc : AS → Ctl → Prop} :
    NodeZ (PB false) exe (Body.wCall (_root_.Executable.labels exe).label J Kc) Spike.Lib.X64.Print.x0 :=
  nodeZ_b hp (l := "scc_rt_print") (off := 0) (by zb) (by zb)

set_option maxHeartbeats 1600000 in
/-- **`print`'s nodes are before the store** (`hZP`): at a node with `Print.N`'s pc and offsets and any
invariant `J`. -/
theorem print_b {c0 : Ctl} {rbp0 ra : BitVec 64} {J : AS → Ctl → Prop} (i : Print.PN) :
    NodeZ (PB false) exe
      ⟨(Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).pc,
        (Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).o, J⟩ (PrintF.FA.blkN i) := by
  cases i
  · exact nodeZ_b hp (l := "scc_rt_print") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.entry") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.loop") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.loop") (off := 20) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.write") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.write") (off := 20) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.write") (off := 22) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.write") (off := 42) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.chk2") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.chk2") (off := 16) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.chk3") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.chk3") (off := 16) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.adv") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.fail") (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".Lscc_rt_print.done") (off := 0) (by zb) (by zb)

/-- **The child's stub is before the store** (`seg_childStubH`'s `hZc`). -/
theorem child_b {cW : Ctl} {w : Child.Words} {tp sp0 : BitVec 64} (i : CN) :
    NodeZ (PB false) exe (cN (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i) := by
  cases i
  · exact nodeZ_b hp (l := x25L) (off := 96) (by zb) (by zb)
  · exact nodeZ_b hp (l := x25L) (off := 99) (by zb) (by zb)
  · exact nodeZ_b hp (l := chL) (off := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := chL) (off := 2) (by zb) (by zb)

end Inst

/-- `helloPass` holds somewhere: before the store on a frame (inhabitation). -/
example (s : State) (h : ¬ helloPassT s) (c : Ctl) (fr : TermRun.Frame) : helloPass s c [fr] :=
  ⟨fun h' => absurd h' h, fun ⟨h1, _⟩ => absurd h1 (List.cons_ne_nil _ _)⟩

end Spike.Lib.X64.Flow.Worker.Hello.Pass

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Pass.print_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Pass.print_b
