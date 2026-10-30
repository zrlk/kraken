/-
**The worker's store is published and ordered below the spawn**
(`spawn_view_lt`): at the source spawn, `helloC`'s `mviewS` and `obS` of the
spawned worker are below the source memory size, given strict view bounds on
main's pre-spawn thread (`SpawnVLt`).

The existing run invariants bound source views by the memory size only
non-strictly (`TermViewInv.VSB`), so the strict bound is a premise on main's
thread before the spawn. The spawn keeps memory; the child's views are main's
after `dmb sy` (`TermSpawnStep.spawnS`), which raises `vPreBase` and
`vRelSt` to at most the join of the old ones and keeps `coh`, and its argument
words are bumped to that `vRelSt` (`TermSpawn.bumpW`).

- `SpawnVLt th a n`: `th`'s scalar views and its coherence at `a` below `n`.
- `KidVLt vs w a n`: the same for the child's views `vs`, and its pointer word
  `w`'s view and read timestamp.
- `store_lt`: `KidVLt` bounds the store's `storeMview` and `storeOb`.
- `kidVLt_spawnKid`: the child of a `SpawnVLt` thread is `KidVLt` with any
  argument word whose view and read timestamp are below `n`, bumped.
- `spawn_view_lt`: the two together at the spawned child.
-/
import Spike.Lib.WorkerSrc

namespace Spike.Lib.SpawnViewLt

open CoreLang CoreTerm TermRun
open WeakMem (VState Address Ts Arch)
open Spike.Lib.WorkerSrc

/-- **Strict view bounds on a source thread**: its scalar views and its
coherence at `a` are below `n`. -/
def SpawnVLt (th : TTh) (a : Address) (n : Nat) : Prop :=
  th.vs.vRd < n ∧ th.vs.vWr < n ∧ th.vs.vCtrl < n ∧ th.vs.vPreBase < n ∧ th.vs.vRelSt < n ∧ th.vs.coh a < n

/-- **Strict bounds at the child**: the scalar views and coherence at `a`
below `n`, and the pointer word's view and read timestamp. -/
def KidVLt (vs : VState) (w : Word) (a : Address) (n : Nat) : Prop :=
  vs.vRd < n ∧ vs.vWr < n ∧ vs.vCtrl < n ∧ vs.vPreBase < n ∧ vs.vRelSt < n ∧ vs.coh a < n ∧
    w.view < n ∧ w.rts < n

/-- **The worker's store at `KidVLt` views publishes and is ordered below
`n`.** -/
theorem store_lt {vs : VState} {w : Word} {a : Address} {n : Nat} (k : Promises.Knobs) (arch : Arch)
    (h : KidVLt vs w a n) :
    Promises.storeMview (wTh vs w) (dataE 1 one) [0] true < n ∧
      Promises.storeOb k arch (wTh vs w) a (dataE 1 one) [0] < n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hd : dataE 1 one = .const (.num 1) := rfl
  have hr0 : (wTh vs w).regs 0 = w := rfl
  refine ⟨?_, ?_⟩
  · simp only [Promises.storeMview, hd, Promises.depView, List.foldl, hr0]
    simp only [wTh, ite_true]
    simp only [WeakMem.Ts] at *; omega
  · simp only [Promises.storeOb, hd, Promises.depView, Promises.depRts, List.foldl, List.append_nil, hr0]
    simp only [wTh]
    split <;> split <;> simp only [WeakMem.Ts] at * <;> omega

/-- **The child of a `SpawnVLt` thread is `KidVLt`**: its views are the
parent's after `dmb sy` with `mine := []`; its argument word `w` (view and
read timestamp below `n`) bumped to the post-barrier `vRelSt`. -/
theorem kidVLt_spawnKid {c : Cfg} {th : TTh} {a : Address} {n : Nat} (h : SpawnVLt th a n) {w : Word}
    (hw : w.view < n ∧ w.rts < n) :
    KidVLt { (TermSpawnStep.spawnS c th).vs with mine := [] }
      (TermSpawn.bumpW (TermSpawnStep.spawnS c th).vs.vRelSt w) a n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [KidVLt, TermSpawnStep.spawnS, fenceS, Promises.stepFence, mth, stOf, TermSpawn.bumpW]
  simp only [WeakMem.Ts] at *; omega

/-- **`spawn_view_lt`**: the spawned child `spawnKid c i th f ts T ws`, its
argument words `ws` (each of view and read timestamp below `n`, e.g.
constants), its first argument word `w1`: `helloC`'s store bounds at the
child are below `n`, given `SpawnVLt th a n`. -/
theorem spawn_view_lt {c : Cfg} {i : Nat} {th : TTh} {f : String} {ts : List Ty} {T : Ty} {ws : List Word}
    {a : Address} {n : Nat} (h : SpawnVLt th a n) (hws : ∀ w ∈ ws, w.view < n ∧ w.rts < n)
    {w1 : Word} {rest : List Word} (hk : (TermSpawnStep.spawnKid c i th f ts T ws).env = [("a", T, w1 :: rest)])
    (k : Promises.Knobs) (arch : Arch) :
    Promises.storeMview (wTh (TermSpawnStep.spawnKid c i th f ts T ws).vs w1) (dataE 1 one) [0] true < n ∧
      Promises.storeOb k arch (wTh (TermSpawnStep.spawnKid c i th f ts T ws).vs w1) a (dataE 1 one) [0] < n := by
  simp only [TermSpawnStep.spawnKid, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hk
  obtain ⟨w0, ws', rfl, -⟩ : ∃ w0 ws', ws = w0 :: ws' ∧ True := by
    cases ws with
    | nil => simp at hk
    | cons w0 ws' => exact ⟨w0, ws', rfl, trivial⟩
  simp only [List.map_cons, List.cons.injEq] at hk
  obtain ⟨rfl, -⟩ := hk
  exact store_lt k arch (kidVLt_spawnKid h (hws w0 (List.mem_cons_self ..)))

/-- **The spawn step's configuration**: memory kept, the child appended
after the parent's slot. -/
theorem spawnCfg_facts {c : Cfg} {i : Nat} {th : TTh} {x : String} {e : Expr} {f : String} {ts : List Ty}
    {T : Ty} {ws : List Word} :
    (TermSpawnStep.spawnCfg c i th x e f ts T ws).mem = c.mem ∧
      (TermSpawnStep.spawnCfg c i th x e f ts T ws).ths[c.ths.size]? =
        some (TermSpawnStep.spawnKid c i th f ts T ws) := by
  refine ⟨rfl, ?_⟩
  simp only [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, Array.getElem?_push, Array.size_set!]
  simp

/-- **`hview`'s form at one spawn step**: if `s'` is thread `i`'s spawn of
`s` (`SrcSem.SpawnBy`'s shape), `s1` its child at slot `s.ths.size`, with
first argument word `w1`, and the spawning thread is `SpawnVLt` at `c`'s
address `a` below `s.mem.size`, the worker's store is published and ordered
below `s'.mem.size`. -/
theorem hview_of_spawnCfg {s : Cfg} {i : Nat} {th : TTh} {x : String} {e : Expr} {f : String} {ts : List Ty}
    {T : Ty} {ws : List Word} {a : Address} (h : SpawnVLt th a s.mem.size)
    (hws : ∀ w ∈ ws, w.view < s.mem.size ∧ w.rts < s.mem.size) {s1 : TTh}
    (hs1 : (TermSpawnStep.spawnCfg s i th x e f ts T ws).ths[s.ths.size]? = some s1)
    {w1 : Word} {rest : List Word} (henv : s1.env = [("a", T, w1 :: rest)]) (k : Promises.Knobs) (arch : Arch) :
    Promises.storeMview (wTh s1.vs w1) (dataE 1 one) [0] true <
        (TermSpawnStep.spawnCfg s i th x e f ts T ws).mem.size ∧
      Promises.storeOb k arch (wTh s1.vs w1) a (dataE 1 one) [0] <
        (TermSpawnStep.spawnCfg s i th x e f ts T ws).mem.size := by
  obtain ⟨hm, hk⟩ := spawnCfg_facts (th := th) (x := x) (e := e) (f := f) (ts := ts) (T := T) (ws := ws)
  rw [hk] at hs1
  cases hs1
  rw [hm]
  exact spawn_view_lt h hws henv k arch

/-- info: 'Spike.Lib.SpawnViewLt.spawn_view_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_view_lt

/-- info: 'Spike.Lib.SpawnViewLt.hview_of_spawnCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hview_of_spawnCfg

end Spike.Lib.SpawnViewLt
