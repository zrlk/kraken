/-
**wake.w on AArch64: the worker's relation after the spawn**: the data `PT1`, `atUnpk`, `atTexit` of `WakeRel` for the
worker, over the worker's rows (`Spike/Lib/SegThr.lean`, `OutT`).

- `wkTail`, `wkBody`: the worker at its spawn (the tail call of `worker`)
  and its body in `wakeSrc` (`split a c j` then `WorkerSrc.wkStore`);
  `WTerm`: the terms the source worker is ever at; `EnvBody`, `EnvCJ`: its
  environment before and after the split.
- `WSide`: per ghost `w`, the memory side `ms w` of the worker's rows and an
  invariant `Wi w` of thread states and source controls closed under the
  rows (`OutT … (Wi w)`): what the worker's whole `SegT`, from the child's
  start through `thr_worker`'s `exit`, gives (`WSide.ofSegT`: a `SegT` to
  the empty fragment is such an invariant).
- `PT1`: the worker's per-thread relation: the thread state and the source
  worker's control in `Wi w`, the source worker on one frame with no type
  variables at a worker term.
- `atUnpk`: the source worker at `let w = unpark j in ret `;
  `atTexit`: the target worker at an `exit` system call.
-/
import Spike.Lib.WakePost1
import Spike.Lib.SegThr
import Spike.Lib.WorkerSrc

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc

/-! ## The worker's terms -/

/-- **The worker's body** in `wakeSrc`. -/
def wkBody : Expr := .split (.var "a") "c" "j" wkStore

/-- `wakeSrc`'s worker has body `wkBody`. -/
theorem wakeSrc_worker : (wakeSrc.find? (·.name == "worker")).map (·.body) = some wkBody := rfl

/-- **The source worker at its spawn** (`TermSpawnStep.spawnKid`): the tail
call of `worker` on its argument. -/
def wkTail : Expr := .tail "worker" [] (.var "a") []

/-- **The source worker before its split**: at its spawn or at its body. -/
def PreSplit (e : Expr) : Prop := e = wkTail ∨ e = wkBody

/-- **The terms the source worker is ever at.** -/
def WTerm (e : Expr) : Prop := e = wkTail ∨ e = wkBody ∨ e = wkStore ∨ e = wkUnpark ∨ e = .ret .unit

/-! ## The worker's side -/

/-- **The worker's side of the relation**, per ghost record `w` of `ι`: the
memory side of its rows (the placement `lbl w`), and an invariant closed
under them. -/
structure WSide (ι : Type) where
  lbl : ι → WeakMem.AllocLabel → Option Nat
  ms : ι → MemSide isaLSE2
  Wi : ι → Frag isaLSE2
  closed : ∀ w s c, Wi w s c → OutT wakeSrc (lbl w) (ms w) (Wi w) s c
  /-- The worker's pointer word for `c` (the first component of its
  argument). -/
  cw : ι → TermRun.Word
  /-- The source memory's size at the spawn (`SpawnRec.S` of the spawn's
  record, `WCompat.S`): the source worker's promises are at or after it. -/
  S : ι → Nat

/-- **A `SegT` to the empty fragment** (the worker's whole segment: it ends
at the thread's `exit`, which has no successor) gives an invariant closed
under the rows. -/
theorem closed_of_segT {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P : Frag isaLSE2}
    (h : SegT wakeSrc lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag isaLSE2, (∀ s c, P s c → inv s c) ∧ ∀ s c, inv s c → OutT wakeSrc lbl ms inv s c := by
  obtain ⟨inv, hP, hi⟩ := h
  exact ⟨inv, hP, fun s c h => (hi s c h).mono fun _ _ h => h.resolve_right id⟩

variable {ι : Type}

/-- main's thread id word (`WakeT1.wake_me`). -/
def mainTidW : WeakMem.Val := .loc ⟨mainTidLbl 2, 0⟩ 0

/-- **The worker's environment at its body**: `a` is the pair of the
pointer word `cw` for `c` (a one-word cell, one word wide) and main's
thread id. -/
def EnvBody (cw : TermRun.Word) (env : TermRun.Env) : Prop :=
  ∃ u v us jw, TermRun.evalAt env (.var "a") = some (.prod u v, [cw, jw]) ∧ TermRun.accs u = some us ∧
    TermRun.nWords us = 1 ∧ (∃ μ u', CoreTerm.cellOf u = some (μ, u') ∧ TermRun.accs u' = some [.one]) ∧
    jw.val = mainTidW

/-- **The worker's environment after the split**: `c` is `cw`, a one-word
cell, and `j` main's thread id. -/
def EnvCJ (cw : TermRun.Word) (env : TermRun.Env) : Prop :=
  (∃ t μ u, TermRun.evalAt env (.var "c") = some (t, [cw]) ∧ CoreTerm.cellOf t = some (μ, u) ∧
    TermRun.accs u = some [.one]) ∧
  ∃ rt jw, TermRun.evalAt env (.var "j") = some (rt, [jw]) ∧ jw.val = mainTidW

/-- **The worker's per-thread relation** (`WakeRel.PT1`): its state and the
source worker's control in the invariant, the source worker on one frame,
with no type variables, at a worker term, its environment binding `c` and
`j` (`EnvBody` before the split, `EnvCJ` after), with at most one
promise, which is a source message at or after the spawn (`D.S w`) to the
address of the pointer word `D.cw w` (the flag `c`'s); the target worker's
promises distinct. At the spawn: the child at the start of `Wi`, `s1` the
spawned thread (term `wkTail`, `EnvBody`, no promise; the source-promise
conjunct is `fun k hk => by simp at hk`, the last `List.nodup_nil`). -/
def PT1 (D : WSide ι) (w : ι) (_tm : Memory) (sm : WeakMem.Memory) (t1 : Thread isaLSE2)
    (s1 : TermRun.TTh) : Prop :=
  D.Wi w t1.st (Ctl.of s1) ∧ s1.stack = [] ∧ s1.σs = [] ∧ WTerm s1.term ∧
    (PreSplit s1.term → EnvBody (D.cw w) s1.env) ∧ (¬ PreSplit s1.term → EnvCJ (D.cw w) s1.env) ∧
    s1.promises.length ≤ 1 ∧
    (∀ k ∈ s1.promises, D.S w ≤ k ∧ ∃ m : WeakMem.Msg, sm[k]? = some m ∧ (D.cw w).val = .loc m.loc 0) ∧
    t1.prom.Nodup

/-- **The worker at its unpark row** (`WakeRel.atUnpk`): the source worker
at `let w = unpark j in ret `. -/
def atUnpk (_t : Cfg) (s : TermRun.Cfg) : Prop := ∃ s1, s.ths[1]? = some s1 ∧ s1.term = wkUnpark

/-- **The worker at its exit row** (`WakeRel.atTexit`): the target worker at
an `exit` system call. -/
def atTexit (t : Cfg) (_s : TermRun.Cfg) : Prop :=
  ∃ t1, t.1.threads[1]? = some t1 ∧ abi.atSys t1.st = true ∧ callOf abi t1 = some .exit

/-- **`worker_done`'s facts** for a relation whose `atTexit` is `atTexit`:
the call by definition, the kernel relation by `kr_exit1`. -/
theorem texitFacts {Q : WakeRel} (hx : Q.atTexit = atTexit)
    (hk : ∀ w t s, Q.KR w t s → Q.atTexit t s → Q.KR w (t.1, t.2.set 1 .exited) s) :
    WakePost1.TexitFacts Q :=
  ⟨fun t s h => by rw [hx] at h; exact h, hk⟩

end Spike.Lib.WakeW1
