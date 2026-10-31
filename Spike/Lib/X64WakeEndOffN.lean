/-
**wake.w's x86-64 worker never at the program's end, at every node** (the
per-node half of `Spike/Lib/A64WakeEndOff.lean`): `EndOff exe kp`
(`Spike/Lib/X64WakeEndOff.lean`) at every node of the child's segments,
decided per node on wake.w's cells (`nodeChk`, through `endOff_at`), and
with `wakePass` the fragment `AbOffZ.wakeZE exe kp` for `seg_childPreNN`.

- `nodeChk l off blk`: the node's bytes `off .. off + |blk|` after `l` are
  decided by `abChk`, and each of the block's cell offsets is below its
  size; `nodeChk_spec`.
- `nodeZ_end`, `nodeZ_end0`, `pro_end`: a node (at `l + off`, at `l`), a
  prologue (bytes `0 .. 35` after its label) with a decided check.
- `head_end`, `wk_end`, `unpk_end`, `tail_end`: each function's nodes.
- `thrZ_end`, `cZ_end`: at every node of the thread worker's run and of the
  child's stub (`X64WakeZXA`'s `hE`, `hEc`).
- `childThrZE`, `cZE`: `seg_childPreNN`'s premises at `Z := AbOffZ.wakeZE exe
  kp`.

**Unlike AArch64** (forced by the x64 shape): a node's pcs are its block's
byte offsets `n.pc + cellOff blk k` (AArch64: `n.pc + 4k`, `k < len`), so
the check `nodeChk` covers the block's whole byte extent and its cell
offsets (AArch64: `abChk l k0 len` alone); the node offsets are the byte
offsets of `X64WakePass`'s nodes (AArch64: instruction indices). A prologue
is its label's bytes `0 .. 35` (AArch64: the 11 instructions at its stack
check, through `labelGap`). `wakeZE` is `AbOffZ.wakeZE` (AArch64: defined
here), and `nodeZ_and`, `thrZ_and` are `AbOffZ`'s.
-/
import Spike.Lib.X64WakeAbOffZ

namespace Spike.Lib.X64.Flow.Worker.Wake.EndOff

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZ thrJ)
open Spike.Lib.X64.WakePh.WcClone (x21L)
open Spike.Lib.X64.WakePh.Child (cN chL)
open Spike.Lib.X64.Flow.Worker.Wake.Child (kidC cBlk)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerTy wc1)
open Spike.Lib.X64.Flow.Worker.Wake.AbOffAt (abChk)
open Spike.Lib.X64.Flow.Worker.Wake.AbOffZ (wakeZE nodeZ_and thrZ_and)

/-- **A node's bytes, decided**: the bytes `off .. off + |blk|` after `l`
pass `abChk`, and every cell offset of the block is below its size. -/
def nodeChk (l : Label) (off : Nat) (blk : List (Directive × Nat)) : Bool :=
  abChk l off (cellOff blk blk.length) &&
    (List.range blk.length).all fun k => decide (cellOff blk k < cellOff blk blk.length)

theorem nodeChk_spec {l : Label} {off : Nat} {blk : List (Directive × Nat)} (h : nodeChk l off blk = true) :
    abChk l off (cellOff blk blk.length) = true ∧ ∀ k, k < blk.length → cellOff blk k < cellOff blk blk.length := by
  simp only [nodeChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe SccCode.wakeCells kp)
include hp

/-- **Off the end at a node** at `off` bytes after `l`, decided. -/
theorem nodeZ_end {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off) (hchk : nodeChk l off blk = true) :
    NodeZ (EndOff exe kp) exe n blk :=
  fun _ _ _ k hk _ hs _ => endOff_at hp (nodeChk_spec hchk).1 ((nodeChk_spec hchk).2 k hk) (by rw [hs, hpc])

/-- **Off the end at a node at a label.** -/
theorem nodeZ_end0 {n : ND} {blk : List (Directive × Nat)} {l : Label}
    (hpc : n.pc = (_root_.Executable.labels exe).label l) (hchk : nodeChk l 0 blk = true) :
    NodeZ (EndOff exe kp) exe n blk :=
  nodeZ_end hp (by rw [hpc]; exact (Int64.add_zero _).symm) hchk

/-- **Off the end at a prologue** (bytes `0 .. 35` after `fn`). -/
theorem pro_end {fn : Label} (hchk : abChk fn 0 36 = true) {J : AS → Ctl → Prop} :
    ∀ (s : State) σ c (k : Nat), k ≤ 35 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat k → J σ c → EndOff exe kp s c := by
  intro s σ c k hk _ hs _
  refine endOff_at hp hchk (k := k) (by omega) ?_
  rw [hs, Int64.add_assoc, ← Int64.ofNat_add, Nat.zero_add]

/-- Off the end at `scc_rt_thr_worker`'s head. -/
theorem head_end {c0 c1 : Ctl} {A B tp sp0 : BitVec 64} (i : ThrHeadW.TN) :
    NodeZ (EndOff exe kp) exe (ThrHeadW.tN (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0)
      (fun _ c => c = c1) i) (ThrHeadW.blkN i) := by
  cases i
  · refine nodeZ_end0 hp (l := ".Lscc_rt_thr_worker.entry") (by rfl) (by decide +kernel)
  · exact Pass.nodeZ_nil

/-- Off the end at `wc_worker`'s nodes. -/
theorem wk_end {c1 c2 c3 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (i : WkTailW.PN) :
    NodeZ (EndOff exe kp) exe (WkTailW.N (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp sp i)
      (WkTailW.blkN i) := by
  cases i
  · refine nodeZ_end0 hp (l := ".Lwc_worker.entry") (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lwc_worker.entry") (off := 11) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lwc_worker.entry") (off := 14) (by rfl) (by decide +kernel)
  · exact Pass.nodeZ_nil
  · refine nodeZ_end0 hp (l := ".Lwc_worker.x14") (by rfl) (by decide +kernel)

/-- Off the end at `scc_rt_unpark`'s nodes. -/
theorem unpk_end {c2 c3 : Ctl} {B rbp1 ra1 tp : BitVec 64} (i : Unpark.PN) :
    NodeZ (EndOff exe kp) exe (Unpark.N (_root_.Executable.labels exe).label c2 c3 B rbp1 ra1 tp i)
      (Unpark.blkN i) := by
  cases i
  · refine nodeZ_end0 hp (l := "scc_rt_unpark") (by rfl) (by decide +kernel)
  · refine nodeZ_end0 hp (l := ".Lscc_rt_unpark.entry") (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_unpark.entry") (off := 11) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_unpark.entry") (off := 15) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_unpark.entry") (off := 35) (by rfl) (by decide +kernel)
  · refine nodeZ_end0 hp (l := ".Lscc_rt_unpark.wake") (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_unpark.wake") (off := 62) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_unpark.wake") (off := 64) (by rfl) (by decide +kernel)
  · refine nodeZ_end0 hp (l := ".Lscc_rt_unpark.done") (by rfl) (by decide +kernel)

/-- Off the end at `scc_rt_thr_worker`'s tail. -/
theorem tail_end {c3 : Ctl} {tp sp0 : BitVec 64} (i : ThrTailW.PN) :
    NodeZ (EndOff exe kp) exe (ThrTailW.N (_root_.Executable.labels exe).label c3 tp sp0 i) (ThrTailW.blkN i) := by
  cases i
  · refine nodeZ_end0 hp (l := ".Lscc_rt_thr_worker.x12") (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_thr_worker.x12") (off := 9) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_thr_worker.x12") (off := 24) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_thr_worker.x12") (off := 28) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := ".Lscc_rt_thr_worker.x12") (off := 40) (by rfl) (by decide +kernel)

/-- **Off the end at every node of the thread worker's run** (`X64WakeZXA`'s
`hE`). -/
theorem thrZ_end {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} :
    ThrZ (EndOff exe kp) exe c0 c1 c2 c3 A B tp sp0 where
  pro := pro_end hp (fn := "scc_rt_thr_worker") (by decide +kernel)
  head := head_end hp
  wpro _ _ := pro_end hp (fn := "wc_worker") (by decide +kernel)
  wk _ _ _ := wk_end hp
  unpk _ _ := unpk_end hp
  tail := tail_end hp

/-- **Off the end at the child's stub** (`X64WakeZXA`'s `hEc`). -/
theorem cZ_end {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (EndOff exe kp) exe (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  intro i
  cases i
  · refine nodeZ_end hp (l := x21L) (off := 48) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := x21L) (off := 51) (by rfl) (by decide +kernel)
  · refine nodeZ_end0 hp (l := chL) (by rfl) (by decide +kernel)
  · refine nodeZ_end hp (l := chL) (off := 2) (by rfl) (by decide +kernel)

/-- **`wakeZE` at the spawned child's nodes** (`seg_childPreNN`'s `ThrZ`
premise at `Z := wakeZE exe kp`). -/
theorem childThrZE (T : Ty) (w1 w2 : TermRun.Word) (A B tp sp0 : BitVec 64) :
    ThrZ (wakeZE exe kp) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_and (Pass.childThrZ hp T w1 w2 A B tp sp0) (thrZ_end hp)

/-- **`wakeZE` at the child's stub** (`seg_childPreNN`'s stub premise). -/
theorem cZE (T : Ty) (w1 w2 : TermRun.Word) {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (wakeZE exe kp) exe (cN (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i) (cBlk i) :=
  fun i => nodeZ_and (Pass.cZ_pass hp (Pass.kidC_not T w1 w2) i) (cZ_end hp i)

end Inst

end Spike.Lib.X64.Flow.Worker.Wake.EndOff

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.EndOff.thrZ_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.EndOff.thrZ_end

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.EndOff.cZ_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.EndOff.cZ_end

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.EndOff.childThrZE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.EndOff.childThrZE

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.EndOff.cZE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.EndOff.cZE
