/-
**wake.w's x86-64 worker off the `writeErr` and `threads` abort exits, at
every node** (the per-node half of `Spike/Lib/A64WakeAbOffW.lean`):
`AbOffL lab` (`Spike/Lib/X64AbOffLDef.lean`) at every node of the child's
segments, decided per node on wake.w's cells (`EndOff.nodeChk`, through
`AbOffAt.abOff_at`), and with `wakePass` the fragment `AbOffZ.wakeZ lab` for
`seg_childPreNN`.

- `nodeZ_ab`, `nodeZ_ab0`, `pro_ab`: a node (at `l + off`, at `l`), a
  prologue (bytes `0 .. 35` after its label) with a decided check.
- `head_ab`, `wk_ab`, `unpk_ab`, `tail_ab`: each function's nodes.
- `thrZ_ab`, `cZ_ab`: at every node of the thread worker's run and of the
  child's stub (`X64WakeZXA`'s `hAb`, `hAbc`).
- `childThrZW`, `cZW`: `seg_childPreNN`'s premises at `Z := AbOffZ.wakeZ
  lab`.
- `hab1_of_wakeZ`: `hab1` from `wakeZ` at `RuntimeLayout.ofPlaceWX` (the
  AArch64 `hab1_of`'s premise), through `X64WakeAbOffW.hab1_of`.

**Unlike AArch64** (forced by the x64 shape): a node's pcs are its block's
byte offsets (AArch64: `n.pc + 4k`), so the check is `EndOff.nodeChk` over
the block's byte extent (AArch64: `abChk l k0 len`); the node offsets are
`X64WakePass`'s byte offsets; a prologue is its label's bytes `0 .. 35`
(AArch64: 11 instructions at its stack check, through `labelGap`). `wakeZ`,
`nodeZ_and`, `thrZ_and` are `AbOffZ`'s (AArch64: defined here), and
`marks_target`, `hab1_of` are `X64WakeAbOffW`'s (AArch64: here, `hab1_of` at
`wakeZ`; here also `hab1_of_wakeZ`).
-/
import Spike.Lib.X64WakeEndOffN
import Spike.Lib.X64WakeAbOffW

namespace Spike.Lib.X64.Flow.Worker.Wake.AbOffW

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
open Spike.Lib.X64.Flow.Worker.Wake.AbOffAt (abChk abOff_at)
open Spike.Lib.X64.Flow.Worker.Wake.AbOffZ (wakeZ nodeZ_and thrZ_and)
open Spike.Lib.X64.Flow.Worker.Wake.EndOff (nodeChk nodeChk_spec)
open Spike.Lib.X64AbOffL (AbOffL)

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe SccCode.wakeCells kp)
include hp

/-- **`AbOffL` at a node** at `off` bytes after `l`, decided. -/
theorem nodeZ_ab {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off) (hchk : nodeChk l off blk = true) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe n blk :=
  fun _ _ _ k hk _ hs _ => abOff_at hp (nodeChk_spec hchk).1 ((nodeChk_spec hchk).2 k hk) (by rw [hs, hpc])

/-- **`AbOffL` at a node at a label.** -/
theorem nodeZ_ab0 {n : ND} {blk : List (Directive × Nat)} {l : Label}
    (hpc : n.pc = (_root_.Executable.labels exe).label l) (hchk : nodeChk l 0 blk = true) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe n blk :=
  nodeZ_ab hp (by rw [hpc]; exact (Int64.add_zero _).symm) hchk

/-- **`AbOffL` at a prologue** (bytes `0 .. 35` after `fn`). -/
theorem pro_ab {fn : Label} (hchk : abChk fn 0 36 = true) {J : AS → Ctl → Prop} :
    ∀ (s : State) σ c (k : Nat), k ≤ 35 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat k → J σ c →
        AbOffL (_root_.Executable.labels exe).label s c := by
  intro s σ c k hk _ hs _
  refine abOff_at hp hchk (k := k) (by omega) ?_
  rw [hs, Int64.add_assoc, ← Int64.ofNat_add, Nat.zero_add]

/-- `AbOffL` at `scc_rt_thr_worker`'s head. -/
theorem head_ab {c0 c1 : Ctl} {A B tp sp0 : BitVec 64} (i : ThrHeadW.TN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (ThrHeadW.tN (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0) (fun _ c => c = c1) i)
      (ThrHeadW.blkN i) := by
  cases i
  · refine nodeZ_ab0 hp (l := ".Lscc_rt_thr_worker.entry") (by rfl) (by decide +kernel)
  · exact Pass.nodeZ_nil

/-- `AbOffL` at `wc_worker`'s nodes. -/
theorem wk_ab {c1 c2 c3 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (i : WkTailW.PN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (WkTailW.N (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp sp i) (WkTailW.blkN i) := by
  cases i
  · refine nodeZ_ab0 hp (l := ".Lwc_worker.entry") (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lwc_worker.entry") (off := 11) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lwc_worker.entry") (off := 14) (by rfl) (by decide +kernel)
  · exact Pass.nodeZ_nil
  · refine nodeZ_ab0 hp (l := ".Lwc_worker.x14") (by rfl) (by decide +kernel)

/-- `AbOffL` at `scc_rt_unpark`'s nodes. -/
theorem unpk_ab {c2 c3 : Ctl} {B rbp1 ra1 tp : BitVec 64} (i : Unpark.PN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (Unpark.N (_root_.Executable.labels exe).label c2 c3 B rbp1 ra1 tp i) (Unpark.blkN i) := by
  cases i
  · refine nodeZ_ab0 hp (l := "scc_rt_unpark") (by rfl) (by decide +kernel)
  · refine nodeZ_ab0 hp (l := ".Lscc_rt_unpark.entry") (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_unpark.entry") (off := 11) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_unpark.entry") (off := 15) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_unpark.entry") (off := 35) (by rfl) (by decide +kernel)
  · refine nodeZ_ab0 hp (l := ".Lscc_rt_unpark.wake") (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_unpark.wake") (off := 62) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_unpark.wake") (off := 64) (by rfl) (by decide +kernel)
  · refine nodeZ_ab0 hp (l := ".Lscc_rt_unpark.done") (by rfl) (by decide +kernel)

/-- `AbOffL` at `scc_rt_thr_worker`'s tail. -/
theorem tail_ab {c3 : Ctl} {tp sp0 : BitVec 64} (i : ThrTailW.PN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (ThrTailW.N (_root_.Executable.labels exe).label c3 tp sp0 i) (ThrTailW.blkN i) := by
  cases i
  · refine nodeZ_ab0 hp (l := ".Lscc_rt_thr_worker.x12") (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_thr_worker.x12") (off := 9) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_thr_worker.x12") (off := 24) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_thr_worker.x12") (off := 28) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := ".Lscc_rt_thr_worker.x12") (off := 40) (by rfl) (by decide +kernel)

/-- **`AbOffL` at every node of the thread worker's run** (`X64WakeZXA`'s
`hAb`). -/
theorem thrZ_ab {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} :
    ThrZ (AbOffL (_root_.Executable.labels exe).label) exe c0 c1 c2 c3 A B tp sp0 where
  pro := pro_ab hp (fn := "scc_rt_thr_worker") (by decide +kernel)
  head := head_ab hp
  wpro _ _ := pro_ab hp (fn := "wc_worker") (by decide +kernel)
  wk _ _ _ := wk_ab hp
  unpk _ _ := unpk_ab hp
  tail := tail_ab hp

/-- **`AbOffL` at the child's stub** (`X64WakeZXA`'s `hAbc`). -/
theorem cZ_ab {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  intro i
  cases i
  · refine nodeZ_ab hp (l := x21L) (off := 48) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := x21L) (off := 51) (by rfl) (by decide +kernel)
  · refine nodeZ_ab0 hp (l := chL) (by rfl) (by decide +kernel)
  · refine nodeZ_ab hp (l := chL) (off := 2) (by rfl) (by decide +kernel)

/-- **`wakeZ` at the spawned child's nodes** (`seg_childPreNN`'s `ThrZ`
premise at `Z := wakeZ`). -/
theorem childThrZW (T : Ty) (w1 w2 : TermRun.Word) (A B tp sp0 : BitVec 64) :
    ThrZ (wakeZ (_root_.Executable.labels exe).label) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_and (Pass.childThrZ hp T w1 w2 A B tp sp0) (thrZ_ab hp)

/-- **`wakeZ` at the child's stub** (`seg_childPreNN`'s stub premise at
`Z := wakeZ`). -/
theorem cZW (T : Ty) (w1 w2 : TermRun.Word) {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (wakeZ (_root_.Executable.labels exe).label) exe
      (cN (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i) (cBlk i) :=
  fun i => nodeZ_and (Pass.cZ_pass hp (Pass.kidC_not T w1 w2) i) (cZ_ab hp i)

end Inst

open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **`hab1` from `wakeZ`** (AArch64 `hab1_of`'s premise): `hab1_of` at the
second conjunct. -/
theorem hab1_of_wakeZ {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (h : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) {ι : Type}
    {PT1 : ι → Memory → WeakMem.Memory → Thread isa → TermRun.TTh → Prop}
    (hZ : ∀ w tm sm t1 s1, PT1 w tm sm t1 s1 →
      ∃ c, wakeZ (RuntimeLayout.ofPlaceWX h i).lab t1.st c) :
    ∀ w tm sm t1 s1, PT1 w tm sm t1 s1 → ∀ k a,
      ((Scc.Sem.X64.target H E).marks asm (RuntimeLayout.ofPlaceWX h i).Λ).abortAt k = some a →
        Scc.Sem.X64.pcOf t1.st = a → k ≠ .writeErr ∧ k ≠ .threads :=
  hab1_of h i hpa fun w tm sm t1 s1 hP =>
    let ⟨c, hc⟩ := hZ w tm sm t1 s1 hP
    ⟨c, AbOffZ.wakeZ_ab hc⟩

end Spike.Lib.X64.Flow.Worker.Wake.AbOffW

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.thrZ_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.thrZ_ab

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.cZ_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.cZ_ab

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.childThrZW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.childThrZW

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.cZW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.cZW

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.hab1_of_wakeZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.hab1_of_wakeZ
