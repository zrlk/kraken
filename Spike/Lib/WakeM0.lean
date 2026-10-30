/-
**wake.w on AArch64: main's relation after the spawn**: the datum `PT0` of `WakeRel` for main, over main's rows
(`Spike/Lib/SegLd.lean`, `OutL`: `Out` and the load-or-stutter row of
`waitLoop`'s acquire load).

- `mTail`, `wlBody`, `wlIf`, `wlPark`, `wlRet` (`WakeMLive`): main's source terms after
  the spawn (the tail call of `waitLoop`, its body, the test of the loaded
  flag, the park and its tail call, the return of `0`); `MTerm`: the terms
  main's source is ever at after the spawn.
- `EnvC cw env`: `c` is bound to the pointer word `cw`, a one-word cell.
- `MSide`: per ghost `w`, the memory side `ms w` of main's rows (placement
  `lbl w`), an invariant `Mi w` of thread states and source controls closed
  under them, main's pointer word `cw w`, and its states off every abort
  site of the marks `μ` (`off`); `closed_of_segL`: a `SegL` to
  the empty fragment (main's whole path after the spawn, which ends at
  `scc_rt_main`'s `exit_group` or at an abort) gives such an invariant.
- `PT0`: main's per-thread relation: its state and source control in
  `Mi w`, the source on one frame with no type variables, at an `MTerm`, with
  `c` bound to `cw w`, no promise, its own thread id (`tidLbl`). It reads
  neither memory, nor `s0.permit`.
- `tid0_of`, `PT0.promises_nil`, `pt0_mem` (`PT0` does not read the memories, so any worker step
  keeps it: `WCompat.pt0`), `mainExit_of_notRet`, `mainLive_of`
  (`WCompat.mainLive`, from a kernel-side fact: main's source returns only
  with the process exited, `LiveK`: `KR` carries `WakeMLive.MainLive`).

`exit_group` keeps the thread state and sets `exited` (`Kernel.sysStep`), and
the source's return is the `exit` event, so main's source is at `wlRet` right
after the target's `exit_group`: a thread-0 relation cannot tell the two apart
and `mainLive` needs the kernel side (`LiveK`, a `KR` fact).
-/
import Spike.Lib.WakeA64
import Spike.Lib.SegLd
import Spike.Lib.WakeMLive

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.WakeMLive (wlRet MainLive)

/-! ## main's terms after the spawn -/

/-- **main at the spawn's continuation**: the tail call of `waitLoop` on `c`. -/
def mTail : Expr := .tail "waitLoop" [] (.var "c") []

/-- `waitLoop`'s park and its tail call. -/
def wlPark : Expr := .let_ "p" (.ext .park .unit) (.tail "waitLoop" [] (.var "c") [])

/-- `waitLoop`'s test of the loaded flag. -/
def wlIf : Expr := .ifeq (.var "d") (.lit 1) wlRet wlPark

/-- **`waitLoop`'s body**: the acquire load of `c`, then the test. -/
def wlBody : Expr := .let_ "d" (.load true (.var "c")) wlIf

/-- `wakeSrc`'s `waitLoop` has body `wlBody`. -/
theorem wakeSrc_waitLoop : (wakeSrc.find? (·.name == "waitLoop")).map (·.body) = some wlBody := rfl

/-- **The terms main's source is ever at after the spawn.** -/
def MTerm (e : Expr) : Prop := e = mTail ∨ e = wlBody ∨ e = wlIf ∨ e = wlPark ∨ e = wlRet

/-- **main's environment after the spawn**: `c` is the pointer word `cw`, a
one-word cell. -/
def EnvC (cw : TermRun.Word) (env : TermRun.Env) : Prop :=
  ∃ t μ u, TermRun.evalAt env (.var "c") = some (t, [cw]) ∧ CoreTerm.cellOf t = some (μ, u) ∧
    TermRun.accs u = some [.one]

/-! ## main's side -/

/-- **main's side of the relation**, per ghost record `w` of `ι`: the memory
side of its rows (the placement `lbl w`), an invariant closed under them,
main's pointer word for `c`, the invariant off every abort site. -/
structure MSide (ι : Type) where
  lbl : ι → WeakMem.AllocLabel → Option Nat
  ms : ι → MemSide isaLSE2
  Mi : ι → Frag isaLSE2
  closed : ∀ w s c, Mi w s c → OutL wakeSrc (lbl w) (ms w) (Mi w) s c
  /-- main's pointer word for `c` (the published cell). -/
  cw : ι → TermRun.Word
  /-- The loaded program's marks. -/
  μ : Marks
  /-- The invariant's states are at no abort site (of any kind): main's path
  after the spawn reaches no abort stub's `exit_group` (its rows accept an
  `exit_group` at every one, so `post_abort` needs all five; at the instance
  from `A64WakeOff.AbOffA`). -/
  off : ∀ w s c, Mi w s c → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a

/-- **A `SegL` to the empty fragment** (main's whole path after the spawn: it
ends at `exit_group`, which has no successor) gives an invariant closed under
the rows. -/
theorem closed_of_segL {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P : Frag isaLSE2}
    (h : SegL wakeSrc lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag isaLSE2, (∀ s c, P s c → inv s c) ∧ ∀ s c, inv s c → OutL wakeSrc lbl ms inv s c := by
  obtain ⟨inv, hP, hi⟩ := h
  exact ⟨inv, hP, fun s c h => (hi s c h).mono fun _ _ h => h.resolve_right id⟩

variable {ι : Type}

/-- **main's per-thread relation** (`WakeRel.PT0`): its state and the source
main's control in the invariant, or main's source at `wlRet` (after its
`exit_group`; `KR`'s `MainLive` excludes it while the process runs), the source on one frame with no type
variables, at a term of `MTerm`, `c` bound to the pointer word, no promise,
its own thread id. Neither memory is read, nor the park permit. -/
def PT0 (D : MSide ι) (w : ι) (_tm : Memory) (_sm : WeakMem.Memory) (t0 : Thread isaLSE2)
    (s0 : TermRun.TTh) : Prop :=
  (D.Mi w t0.st (Ctl.of s0) ∨ s0.term = wlRet) ∧ s0.stack = [] ∧ s0.σs = [] ∧ MTerm s0.term ∧ EnvC (D.cw w) s0.env ∧
    s0.promises = [] ∧ s0.tidLbl = some (mainTidLbl 2)

variable {D : MSide ι} {w : ι}

/-- `PT0` carries main's own thread id (`WCompat.tid0`). -/
theorem tid0_of {tm : Memory} {sm : WeakMem.Memory} {t0 : Thread isaLSE2} {s0 : TermRun.TTh}
    (h : PT0 D w tm sm t0 s0) : s0.tidLbl = some (mainTidLbl 2) := h.2.2.2.2.2.2

/-- `PT0` carries main's empty source promise list (`WCompatX.sp0`). -/
theorem PT0.promises_nil {tm : Memory} {sm : WeakMem.Memory} {t0 : Thread isaLSE2} {s0 : TermRun.TTh}
    (h : PT0 D w tm sm t0 s0) : s0.promises = [] := h.2.2.2.2.2.1

/-- **`PT0` does not read the memories**: it holds at any other pair
(`WCompat.pt0`, whatever a worker step does to them). -/
theorem pt0_mem {tm tm' : Memory} {sm sm' : WeakMem.Memory} {t0 : Thread isaLSE2} {s0 : TermRun.TTh}
    (h : PT0 D w tm sm t0 s0) : PT0 D w tm' sm' t0 s0 := h

/-- **`PT0` does not read the park permit**: it holds at any other pair of
memories with main's source permit replaced (`WCompatX.pt0p`, the worker's
`unpark` setting it). -/
theorem pt0_permit {tm tm' : Memory} {sm sm' : WeakMem.Memory} {t0 : Thread isaLSE2} {s0 : TermRun.TTh}
    (p : Option Nat) (h : PT0 D w tm sm t0 s0) : PT0 D w tm' sm' t0 { s0 with permit := p } := h

/-- **main's source has not returned** when it is not at `wlRet`. -/
theorem mainExit_of_notRet {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} (hs : s.ths = #[s0, s1])
    (hm : MTerm s0.term) (hr : s0.term ≠ wlRet) : SrcSem.mainExit s = [] := by
  unfold SrcSem.mainExit
  rw [hs]
  simp only [List.getElem?_toArray]
  show (match s0.term, s0.stack with
    | .ret a, [] => _
    | _, _ => []) = []
  rcases hm with h | h | h | h | h
  all_goals first | exact absurd h hr | (rw [h]; rfl)

/-- **The kernel-side liveness fact**: `KR` carries `MainLive`
(`Spike/Lib/WakeMLive.lean`; the conjunct, kept by `post_step0` at the
`exit_group`, the only step that brings main's source to `wlRet`). -/
def LiveK (Q : WakeRel) : Prop := ∀ w t s, Q.KR w t s → MainLive t.2 s

/-- **main has not returned while the process runs** (`WCompat.mainLive`),
for a relation whose `PT0` is this file's and whose `KR` has `LiveK`. -/
theorem mainLive_of {Q : WakeRel} {Λ : Scc.Sem.Layout} {D : MSide Q.ι} (hpt : Q.PT0 = PT0 D) (hk : LiveK Q)
    {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) (hx : t.2.exited = none) : SrcSem.mainExit s = [] := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, h1, h2, -, h0, -, -⟩, hK⟩ := h
  simp only [WakeRel.PTw, ↓reduceIte, hpt] at h0
  exact mainExit_of_notRet h2 h0.2.2.2.2.1 (hk w t s hK hx s0 (by rw [h2]; rfl))

end Spike.Lib.WakeM0
