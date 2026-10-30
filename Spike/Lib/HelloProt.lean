/-
**hello's protocols on the words written after the spawn** (`s1_threads.md` §2.2 option B, items 4 and 5, and §1.4). ISA-generic. The
protocol `Prot` argument of `Spike.Lib.Inv2Core.Inv2` for hello.

- `CRec`: the flag `c`'s words (target location `cT`, source address `cS`)
  and the worker's store point on each side (`passT`, `passS`).
- `CProt R C oc`: (item 4) `c`'s messages after the spawn: none
  (`oc = none`), or one on each side (`oc = some (Tc, kc)`), the worker's,
  paired by the map; the target one a mirrored promise iff the source one
  is a promise, and then the worker's on both sides; the worker past its
  store on the target iff on the source, and then neither message a
  promise; both of value `1`; before the store, the source store's view
  and ordering bound below the spawn's source size `S` and a source
  promise's view at least `S - 1` (the G1–G3: what the source
  fulfilment needs).
  The caller's `Inv2Params.frzS` must contain every word of the setup's
  buffer label (both words of `rodata`'s `newBuf`) and `frz` their images
  (the print loop's source loads are then deterministic).
- (Item 5, the permit protocol, is not needed: source `main` never parks,
  D4 abandoned, main's park being a target-only stutter; the park and
  unpark rows need only that `G` allows `0` and `1` at main's permit word.)
- `HelloProt`: the `c` protocol at some `oc`.
-/
import Spike.Lib.Inv2Core

namespace Spike.Lib.HelloProt

open Kraken.Promising Scc.Sem Spike.Lib.Inv2Core

/-- **The flag `c`**: its target word, its source address, and the
worker's store point on each side (true once the worker has executed its
`store rel c 1`, as a fulfilment or an append). -/
structure CRec (I : ISA) where
  cT : Loc
  cS : WeakMem.Address
  passT : I.State → Prop
  passS : TermRun.TTh → Prop
  /-- The message view the source worker's `store rel c 1` publishes at
  the source thread (before the store: the view it would publish there),
  `Promises.storeMview` with the pointer word's view (the store's
  dependency, G1). -/
  mviewS : TermRun.TTh → Nat
  /-- The store's ordering bound at the source thread (`Promises.storeOb`:
  `vPreBase`, the pointer word's read timestamp, `vCtrl`, `coh cS`, and
  under TSO `vRd`, `vWr`; G2). -/
  obS : TermRun.TTh → Nat

/-- **(Item 4) The `c` protocol** at `oc`: `c`'s messages after the spawn
are none (`oc = none`) or exactly one on each side, `Tc` (target) and `kc`
(source), the worker's, with `ts kc = Tc`, both of value `1` (G3). Before
its store the source worker's store publishes and is ordered below the
spawn (`pre_lt`), and a source promise's view is at least `S - 1`
(`prom_view`), so the store can fulfil the promise (`stepStore`:
`mview ≤ m.view`, `ob < kc`). -/
structure CProt {I : ISA} (R : SpawnRec) (C : CRec I) (oc : Option (Nat × Nat)) (tm : Memory) (t1 : Thread I)
    (sm : WeakMem.Memory) (s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat) : Prop where
  /-- The target messages to `c` after the spawn: `Tc` only, the worker's. -/
  tmsg : ∀ k w, tm.get? k = some w → R.T < k → w.loc = C.cT → ∃ kc, oc = some (k, kc) ∧ w.tid = 1
  /-- The source messages to `c` after the spawn: `kc` only. -/
  smsg : ∀ k m, sm[k]? = some m → R.S ≤ k → m.loc = C.cS → ∃ Tc, oc = some (Tc, k)
  /-- `Tc` and `kc` are messages to `c` after the spawn, paired by the map. -/
  some_msg : ∀ Tc kc, oc = some (Tc, kc) →
    R.T < Tc ∧ R.S ≤ kc ∧ ts kc = some Tc ∧ (∃ w, tm.get? Tc = some w ∧ w.loc = C.cT ∧ w.tid = 1 ∧ w.val = 1) ∧
      ∃ m, sm[kc]? = some m ∧ m.loc = C.cS ∧ m.val = .num 1
  /-- A mirrored promise is the worker's, on both sides. -/
  prom_worker : ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp → Tc ∈ t1.prom ∧ kc ∈ s1.promises
  /-- The worker is past its store on the target iff on the source ... -/
  pass_iff : C.passT t1.st ↔ C.passS s1
  /-- ... and then `c` is written and not a promise. -/
  pass_done : C.passT t1.st → ∃ Tc kc, oc = some (Tc, kc) ∧ Tc ∉ tp
  /-- Before it, `c` is unwritten or a mirrored promise. -/
  pass_prom : ¬ C.passT t1.st → ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp
  /-- (G1, G2) Before its store, the source worker's store would publish
  a view and be ordered below the spawn's source size ... -/
  pre_lt : ¬ C.passS s1 → C.mviewS s1 < R.S ∧ C.obS s1 < R.S
  /-- ... and a source promise's view is at least `S - 1`. -/
  prom_view : ∀ Tc kc m, oc = some (Tc, kc) → kc ∈ sp → sm[kc]? = some m → R.S ≤ m.view + 1

set_option linter.unusedVariables false in
/-- **hello's protocol**: the `c` protocol at some `oc`. The `Prot`
argument of `Inv2`.

There is no permit protocol (the former item 5, `PermitProt`, is dropped):
source `main` never parks (D4 abandoned; main's park is a target-only
stutter), and the park and unpark rows (`Park.seg_park`, `Unpark.seg_unpark`)
hold for every old value of main's permit word, needing only that the
runtime invariant `G` allows `0` and `1` there (see `Inv2Core.Inv2Params`).
The arguments `pT`, `t0` and `s0` are unused, kept for interface stability
(to be pruned once wake.w closes). -/
def HelloProt {I : ISA} (R : SpawnRec) (C : CRec I) (pT : Loc) (tm : Memory) (t0 t1 : Thread I)
    (sm : WeakMem.Memory) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat) : Prop :=
  ∃ oc, CProt R C oc tm t1 sm s1 ts tp sp

/-- **At the spawn** (no message after it, no promise, worker before its
store on both sides) the protocol holds with `oc = none`. -/
theorem helloProt_start {I : ISA} {R : SpawnRec} {C : CRec I} {pT : Loc} {tm : Memory} {t0 t1 : Thread I}
    {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {sp : List Nat}
    (hT : tm.last ≤ R.T) (hS : sm.size ≤ R.S) (hpT : ¬ C.passT t1.st) (hpS : ¬ C.passS s1)
    (hlt : C.mviewS s1 < R.S ∧ C.obS s1 < R.S) : HelloProt R C pT tm t0 t1 sm s0 s1 ts [] sp := by
  refine ⟨none, ?_, ?_, ?_, ?_, ⟨fun h => absurd h hpT, fun h => absurd h hpS⟩, fun h => absurd h hpT, ?_, fun _ => hlt, ?_⟩
  · intro k w hk hk'
    have h1 : k ≤ tm.last := Kraken.Promising.Memory.le_last_of_get? hk
    exact absurd (Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt hT hk')) (Nat.lt_irrefl _)
  · intro k m hk hk'
    have := (Array.getElem?_eq_some_iff.mp hk).1
    omega
  · intro _ _ h; cases h
  · intro _ _ h; cases h
  · intro _ _ _ h; cases h
  · intro _ _ _ h; cases h

end Spike.Lib.HelloProt
