/-
**wake.w on AArch64: the owned words after the spawn**:
the datum `own` of `WakeRel` is empty for both threads. No row of either
thread after the spawn reads an owned value (the worker's and main's
runtime words are written as the runtime's for any value runtime memory
may hold, `StOk`, or exchanged for any old value); the owned counters only
matter before the clone (`R1`). The rows' memory sides own nothing too
(`WCompat.own`).

- `wakeOwn`: the empty own map.
- `own_nil`: `WCompat.own` at `(D.ms w).own := fun _ => []`.
- `ownInstr`, `ownSys`, `ownCov`, `ownDisj`: the `WCompat` fields; `own1`: `WCompatX.own1`.
- `post_startO`: `WakeA64.post_start` at `Q.own = wakeOwn`, its own
  hypotheses (`hsub0`, `hsub1`, `hdisj`, `hcov0`, `hcov1`) discharged.
-/
import Spike.Lib.WakeA64

namespace Spike.Lib.WakeOwn

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WakeT1

/-- **The owned words after the spawn**: none, for either thread. -/
-- Empty because every post-spawn row is any-value (checked by grep of `.own`/`OwnAt`/`ownLdop` over
-- A64WakeWorker*, A64WorkerRows, A64Park, A64WakeChild*, A64WakeChildPre, A64WakeParent*, A64WakeSplit,
-- A64WaitLoop, A64WakeMainPost, A64CodeSegs, A64WakeSpawnFail, A64Abort*, A64CfgL, SegLd): a future row
-- reading an owned value must change this and `WCompat.own`'s instance.
def wakeOwn {ι : Type} : ι → Nat → isaLSE2.State → List TermRun.Frame → List (Loc × Val) :=
  fun _ _ _ _ => []

theorem own_nil {ι : Type} (w : ι) (s : isaLSE2.State) : (fun _ => ([] : List (Loc × Val))) s = wakeOwn w 1 s [] :=
  rfl

theorem ownInstr {ι : Type} (w : ι) (s : isaLSE2.State) (tree : EvTree isaLSE2.State) :
    Consumer1.OwnTree (fun s => wakeOwn w 1 s []) (wakeOwn w 1 s []) tree :=
  Consumer1.OwnTree.nil tree

theorem ownSys {ι : Type} (w : ι) (s s' : isaLSE2.State) : wakeOwn w 1 s' [] = wakeOwn w 1 s [] :=
  rfl

/-- `WCompatX.own1`: the worker's owned words at an empty stack are none. -/
theorem own1 {ι : Type} (w : ι) (s : isaLSE2.State) : wakeOwn w 1 s [] = [] :=
  rfl

theorem ownCov {ι : Type} {P : Loc → Prop} (w : ι) (i : Nat) (s : isaLSE2.State) (fs : List TermRun.Frame)
    (L : Loc) (v : Val) (h : (L, v) ∈ wakeOwn w i s fs) : P L :=
  nomatch h

theorem ownDisj {ι : Type} (w : ι) (i j : Nat) (s0 s : isaLSE2.State) (fs fs' : List TermRun.Frame)
    (L : Loc) (v v' : Val) (h : (L, v) ∈ wakeOwn w i s0 fs) (_ : (L, v') ∈ wakeOwn w j s fs') : False :=
  nomatch h

/-- **`post_start` with no owned words**: `WakeA64.post_start` at
`Q.own = wakeOwn`, its own hypotheses discharged. -/
theorem post_startO {Λ : Scc.Sem.Layout} {Q : WakeRel} (hQ : Q.own = wakeOwn) {w : Q.ι}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isaLSE2} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    {j : Nat} (hj : d.1.mem.read? (Q.C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (hPT0 : Q.PT0 w d.1.mem s.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hPT1 : Q.PT1 w d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1)
    (hProt : HelloProt (Q.SR w) (Q.C w) (Q.pT w) d.1.mem (retThread abi (parentPre abi d.2 0 th stack) r)
      (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : Q.KR w (afterClone abi d 0 th stack tls r) s) :
    Q.Post Λ (afterClone abi d 0 th stack tls r) s := by
  refine post_start hSR h1 hs hi hp hmsgs hin hfits hG hb hown hsp0 hsp1 hs0 hs1 hfrz hfoot ?_ ?_ ?_ ?_ ?_
    hj hjl hPT0 hPT1 hProt hKR <;> intros <;> simp_all [wakeOwn]

/-- info: 'Spike.Lib.WakeOwn.post_startO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOwn.post_startO

end Spike.Lib.WakeOwn
