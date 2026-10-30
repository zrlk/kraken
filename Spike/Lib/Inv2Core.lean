/-
**The two-thread relation, generic core** (`s1_threads.md`
§2.2 option B, items 1–3, 6, 7; design note 0.7 (O1)–(O5)). ISA-generic:
it constrains the target memory, the two target threads' views and
promises, the source memory and the two source threads' coherence views
and promises. The per-thread control relation (item 2) and the
program-specific protocols on the words written after the spawn (items 4,
5: for hello, `Spike/Lib/HelloCProt.lean` and `Spike/Lib/HelloPermit.lean`)
are parameters of `Inv2`.

- `SpawnRec`: what is fixed at the spawn: the target memory's last
  timestamp `T` and the source memory's size `S` there, and the placement
  (`lbl`, `lsize`; no allocation after the spawn, so labels are frozen).
- `Inv2Params`: the location sets: the frozen words (`frz` target, `frzS`
  source), each thread's cover set `cov i` (O3: its owned words and the
  frozen words), each thread's footprint `foot i` (O2: where its messages
  may go), and the states at which a thread has no promise (`noProm`,
  item 7: at a `write` or `clone`). A promise is a message of its thread
  after the spawn, so it is in the thread's footprint.
- `CohCoversL`: (O3) the location-restricted cover.
- `InLabel`: a location inside a placed label.
- `Inv2Core`: items 1, 3, 6, 7 and (O1)–(O5), over explicit threads and
  memories.
- `Inv2`: a two-thread target configuration and a two-thread source
  configuration related by `Inv2Core`, a per-thread relation `PT i` and a
  protocol `Prot`.
-/
import Spike.Lib.Consumer1

namespace Spike.Lib.Inv2Core

open Kraken.Promising Scc.Sem

/-- **What is fixed at the spawn**: the target memory's last timestamp `T`
and the source memory's size `S` at the spawn (so the target messages
after the spawn are those above `T`, the source ones those at or above
`S`), and the placement (no label is allocated or placed after the spawn). -/
structure SpawnRec where
  T : Nat
  S : Nat
  lbl : WeakMem.AllocLabel → Option Nat
  lsize : WeakMem.AllocLabel → Nat

/-- **The location sets of the relation.** -/
structure Inv2Params (I : ISA) where
  /-- The frozen target words: the placed words with no message after the
  spawn (item 3; for hello every placed word but `c`). -/
  frz : Loc → Prop
  /-- The frozen source words (item 3). -/
  frzS : WeakMem.Address → Prop
  /-- (O3) Thread `i`'s cover set `L_i`: its owned words and the frozen
  words. -/
  cov : Nat → Loc → Prop
  /-- (O2) Thread `i`'s footprint: every message of thread `i` after the
  spawn is to it (its owned words, the placed words a source step writes,
  the protocol words, private words). -/
  foot : Nat → Loc → Prop
  /-- (Item 7) The states at which a thread has no promise (at a `write`
  or `clone` system call). -/
  noProm : I.State → Prop

/-- **(O3) The location-restricted cover**: the thread's coherence views
cover every message it has not promised to a location in `L`. -/
def CohCoversL (vs : Views) (prom : List Time) (mem : Memory) (L : Loc → Prop) : Prop :=
  ∀ k w, mem.get? k = some w → L w.loc → k ∉ prom → k ≤ vs.getCoh w.loc

/-- The one-thread cover is the cover on every location. -/
theorem CohCoversL.of_cohCoversP {vs : Views} {prom : List Time} {mem : Memory} (h : CohCoversP vs prom mem)
    (L : Loc → Prop) : CohCoversL vs prom mem L :=
  fun k w hk _ hp => h k w hk hp

/-- A smaller location set keeps the cover. -/
theorem CohCoversL.anti {vs : Views} {prom : List Time} {mem : Memory} {L L' : Loc → Prop}
    (h : CohCoversL vs prom mem L) (hL : ∀ l, L' l → L l) : CohCoversL vs prom mem L' :=
  fun k w hk hl hp => h k w hk (hL _ hl) hp

/-- **A location inside a placed label.** -/
def InLabel (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (l : Loc) : Prop :=
  ∃ lb b, lbl lb = some b ∧ (lrange lsize lb b).contains l.addr.toNat

/-- **The generic core of the two-thread relation** over the target memory
`tm`, the target threads `t0` (main) and `t1` (the child), the source
memory `sm`, the source threads `s0` and `s1`, the message map `ts` and the
mirrored promises `tp` (target) and `sp` (source); `own i` is the list of
thread `i`'s owned runtime words with their values. -/
structure Inv2Core {I : ISA} (Λ : Scc.Sem.Layout) (R : SpawnRec) (P : Inv2Params I) (G : Loc → Val → Prop)
    (own : Nat → List (Loc × Val)) (tm : Memory) (t0 t1 : Thread I) (sm : WeakMem.Memory)
    (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat) : Prop where
  /-- (1) The memory relation over the spawn's placement, every target
  promise inside a label mirrored (`tq = []`). -/
  mem : MemRelP Λ R.lbl R.lsize ts tm sm tp [] sp
  /-- (1) The mirrored target promises are the two threads' promises
  inside a label. -/
  tp_prom : ∀ k ∈ tp, k ∈ t0.prom ∨ k ∈ t1.prom
  prom_tp : ∀ k w, (k ∈ t0.prom ∨ k ∈ t1.prom) → tm.get? k = some w → InLabel R.lbl R.lsize w.loc → k ∈ tp
  /-- (1) The source promises are the two source threads'. -/
  sp_prom : ∀ k, k ∈ sp ↔ k ∈ s0.promises ∨ k ∈ s1.promises
  narrow : MemRel.Narrow tm
  memIn : Consumer1.MemIn Λ tm
  fits : Consumer1.MemFits tm
  /-- (6) Every target value satisfies the runtime invariant. (For hello and
  wake, the park and unpark rows, `Park.seg_park` and `Unpark.seg_unpark`,
  rely on `G ⟨pT, 8⟩ 0` and `G ⟨pT, 8⟩ 1` at main's permit word `pT`: the
  only fact about `pT` they use, standing for the dropped permit protocol of
  `HelloProt`.) -/
  memInv : MemInv G tm
  bnd0 : t0.Bnd tm.last
  bnd1 : t1.Bnd tm.last
  /-- (O3) Each thread covers its cover set. -/
  cov0 : CohCoversL t0.views t0.prom tm (P.cov 0)
  cov1 : CohCoversL t1.views t1.prom tm (P.cov 1)
  /-- (3) The frozen words are in both cover sets. -/
  frz_cov : ∀ i l, i < 2 → P.frz l → P.cov i l
  /-- (3) No target message to a frozen word after the spawn ... -/
  frzT : ∀ k w, tm.get? k = some w → R.T < k → ¬ P.frz w.loc
  /-- (3) ... nor a source one ... -/
  frzS : ∀ k m, sm[k]? = some m → R.S ≤ k → ¬ P.frzS m.loc
  /-- (3) ... and both source threads' coherence views cover the frozen
  source words' messages. -/
  scov0 : ∀ k m, sm[k]? = some m → P.frzS m.loc → k ≤ s0.vs.coh m.loc
  scov1 : ∀ k m, sm[k]? = some m → P.frzS m.loc → k ≤ s1.vs.coh m.loc
  /-- (O5) Every target message up to the spawn is thread 0's ... -/
  pre_tid : ∀ k w, tm.get? k = some w → k ≤ R.T → w.tid = 0
  /-- (O5, O2) ... and every later one is thread 0's or 1's, in its
  footprint. -/
  post_foot : ∀ k w, tm.get? k = some w → R.T < k → (w.tid = 0 ∨ w.tid = 1) ∧ P.foot w.tid w.loc
  /-- (O2, O3) One thread's footprint is outside the other's cover set. -/
  foot_cov : ∀ i j l, i < 2 → j < 2 → i ≠ j → P.foot j l → ¬ P.cov i l
  /-- (6, O4) Each thread's owned words read as their values ... -/
  own0 : ExtRows.OwnOk (own 0) tm t0.prom
  own1 : ExtRows.OwnOk (own 1) tm t1.prom
  /-- (O1) ... are disjoint ... -/
  own_disj : ∀ L v v', (L, v) ∈ own 0 → (L, v') ∈ own 1 → False
  /-- (O3) ... and in the owner's cover set. -/
  own_cov : ∀ i L v, i < 2 → (L, v) ∈ own i → P.cov i L
  /-- (7) A promise is the thread's own message after the spawn (so, by
  `post_foot`, in its footprint) ... -/
  prom0 : ∀ k ∈ t0.prom, R.T < k ∧ ∃ w, tm.get? k = some w ∧ w.tid = 0
  prom1 : ∀ k ∈ t1.prom, R.T < k ∧ ∃ w, tm.get? k = some w ∧ w.tid = 1
  /-- (7) ... and there is none at a `write` or `clone`. -/
  noProm0 : P.noProm t0.st → t0.prom = []
  noProm1 : P.noProm t1.st → t1.prom = []
  /-- The spawn is at or before the memory's last timestamp (memory only
  grows; needed for `Inv2Rely.Inv2Core.pre_tid_append`). -/
  T_le : R.T ≤ tm.last
  /-- The spawn is at or before the source memory's size (source memory
  only grows; the source twin of `T_le`). -/
  S_le : R.S ≤ sm.size

/-- **The two-thread relation**: a target configuration of two threads and
a source configuration of two threads, related by the core (`own i` the
words thread `i` owns at its state and its source thread's frames), the
per-thread relation `PT i tm sm` (item 2: the control pairing, `WideSt`,
`Bnd`, the hold; the kernel state is the caller's) and the program's protocol `Prot` on
the words written after the spawn (items 4, 5). -/
def Inv2 {I : ISA} (Λ : Scc.Sem.Layout) (R : SpawnRec) (P : Inv2Params I) (G : Loc → Val → Prop)
    (own : Nat → I.State → List TermRun.Frame → List (Loc × Val))
    (PT : Nat → Memory → WeakMem.Memory → Thread I → TermRun.TTh → Prop)
    (Prot : Memory → Thread I → Thread I → WeakMem.Memory → TermRun.TTh → TermRun.TTh →
      (Nat → Option Nat) → List Nat → List Nat → Prop)
    (c : Config I) (s : TermRun.Cfg) : Prop :=
  ∃ (t0 t1 : Thread I) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat),
    c.threads = #[t0, t1] ∧ s.ths = #[s0, s1] ∧
    Inv2Core Λ R P G (fun i => if i = 0 then own 0 t0.st s0.stack else own 1 t1.st s1.stack)
      c.mem t0 t1 s.mem s0 s1 ts tp sp ∧
    PT 0 c.mem s.mem t0 s0 ∧ PT 1 c.mem s.mem t1 s1 ∧ Prot c.mem t0 t1 s.mem s0 s1 ts tp sp

namespace Inv2Core

variable {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {P : Inv2Params I} {G : Loc → Val → Prop}
  {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {sm : WeakMem.Memory}
  {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- (O2) A target message after the spawn to thread `i`'s cover set is
thread `i`'s. -/
theorem tid_of_cov (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {i k : Nat} {w : Msg} (hi : i < 2)
    (hk : tm.get? k = some w) (hT : R.T < k) (hc : P.cov i w.loc) : w.tid = i := by
  obtain ⟨ht, hf⟩ := h.post_foot k w hk hT
  refine Decidable.byContradiction fun hne => ?_
  have hj : w.tid < 2 := by omega
  exact h.foot_cov i w.tid w.loc hi hj (Ne.symm hne) hf hc

/-- (3) A frozen word's target messages are all at or before the spawn. -/
theorem frz_le (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {k : Nat} {w : Msg}
    (hk : tm.get? k = some w) (hf : P.frz w.loc) : k ≤ R.T :=
  Nat.le_of_not_lt fun hT => h.frzT k w hk hT hf

end Inv2Core

end Spike.Lib.Inv2Core
