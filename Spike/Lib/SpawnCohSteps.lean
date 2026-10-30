/-
**Source coherence at wake's spawn, from the start** (`scov_spawn`): the
companion of `SpawnViewLtSteps.VPre` that gives `SpawnPre.scov0`/`scov1`.

Before the spawn, wake's source has one thread, `main`, and it writes every
message in the source memory, so its coherence covers each of them
(`CohC`): every message `k` not among `main`'s own outstanding promises is
at most `main`'s coherence at the message's location. The start has empty
memory. `new` pushes its cell's `undef` messages and raises coherence to
them, and its initialising store moves coherence to the stored message
(appended or fulfilled). `zero`, `pair`, `publish` (`dmb st`) and the tail
call into `main` keep the memory, the coherence and the promises. A promise
step pushes a message that is one of `main`'s promises. At the spawn, `main`
has no promises, and both the parent and the child take `main`'s coherence
(`spawnS` is a `dmb sy`, which keeps it), so every source message is below
both threads' coherence at its location.

- `CohC`, `VPreC`: the invariant (vacuous once there are two threads).
- `vpreC_init`, `vpreC_step`, `vpreC_run`: it holds along source runs (with
  `VPre`, for `main`'s term).
- `pre1T_vpreC`: any `Pre1T … (R1 ∧ VPre)` strengthened by `VPreC`.
- `scov_spawn`: at `spawnCfg s 0 th0 …` with `th0` promise-free, the
  coherence bound for the spawned configuration's two threads (the form of
  `SpawnPre.scov0`/`scov1`, at every location).
-/
import Spike.Lib.SpawnViewLtSteps
import Spike.Lib.WakePreInv

namespace Spike.Lib.SpawnCohSteps

open CoreLang CoreTerm TermRun
open WeakMem (VState Address Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeA64 (wakeS)
open Spike.Lib.WakeM0 (mTail)
open Spike.Lib.SpawnViewLtSteps
open Spike.Lib.WorkerSrcStep (getElem?_set!_self)

/-! ## The invariant -/

/-- **Coherence covers the memory**: every message not among the promises
`P` is at most the coherence `coh` at its location. -/
def CohM (mem : WeakMem.Memory) (coh : Address → Nat) (P : List Ts) : Prop :=
  ∀ k m, mem[k]? = some m → k ∉ P → k ≤ coh m.loc

/-- `CohM` for main's thread. -/
def CohC (mem : WeakMem.Memory) (th : TTh) : Prop := CohM mem th.vs.coh th.promises

/-- **`p` at the spawn is the pair of `c` and `me`**: at `spawnTerm`, `p`'s
binding is `c`'s and `me`'s, types and words. -/
def PB (th : TTh) : Prop :=
  th.term = spawnTerm → ∃ tc wc tm wm, lookupE th.env "c" = some (tc, wc) ∧ lookupE th.env "me" = some (tm, wm) ∧
    lookupE th.env "p" = some (.prod tc tm, wc ++ wm)

/-- **The source coherence invariant before the spawn**: with one thread,
its coherence covers the memory, and `p` is `c`'s and `me`'s pair at the
spawn. -/
def VPreC (s : Cfg) : Prop := s.ths.size = 1 → ∃ th0, s.ths[0]? = some th0 ∧ CohC s.mem th0 ∧ PB th0

/-! ## Stores and allocations -/

/-- **A one-word store keeps `CohM`.** -/
theorem cohM_store {k : Promises.Knobs} {arch : Arch} {mem mem' : WeakMem.Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (hc : CohM mem th.vs.coh th.promises) (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    CohM mem' th'.vs.coh th'.promises := by
  obtain ⟨t, hcase, hcoh, -, -⟩ := TermStep.stepStore_casesC h
  rw [hcoh]
  intro i m hm hi
  rcases hcase with ⟨rfl, rfl, hp⟩ | ⟨rfl, ht, hp, hlt, m0, hm0, hl0, -, -⟩
  · rw [hp] at hi
    rw [Array.getElem?_push] at hm
    split at hm
    · rename_i he
      cases hm
      simp [he]
    · have hlt := (Array.getElem?_eq_some_iff.mp hm).1
      have := hc i m hm hi
      show i ≤ (if m.loc = a then mem.size else th.vs.coh m.loc)
      by_cases hl : m.loc = a
      · simp only [hl, ite_true]; exact Nat.le_of_lt hlt
      · simp only [hl, ite_false]; exact this
  · rw [hp] at hi
    by_cases he : i = t
    · subst he
      rw [hm0] at hm; cases hm
      simp [hl0]
    · have hi' : i ∉ th.promises := fun h => hi ((List.mem_erase_of_ne he).2 h)
      have := hc i m hm hi'
      show i ≤ (if m.loc = a then t else th.vs.coh m.loc)
      by_cases hl : m.loc = a
      · simp only [hl, ite_true]; rw [hl] at this; exact Nat.le_of_lt (Nat.lt_of_le_of_lt this hlt)
      · simp only [hl, ite_false]; exact this

/-- **`new` of one word keeps `CohM`** (its pushed `undef` message under the
raised coherence, then its store). -/
theorem cohM_alloc {k : Promises.Knobs} {arch : Arch} {lbl : WeakMem.AllocLabel} {ws : List Word} {s s' : St}
    {pw : Word} (hc : CohM s.mem s.vs.coh s.promises) (h : (s', pw) ∈ alloc k arch lbl [.one] ws s) :
    CohM s'.mem s'.vs.coh s'.promises := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, -⟩ := h
  cases ws with
  | nil => simp [storeUnits] at hs2
  | cons w ws =>
    simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at hs2
    obtain ⟨⟨mem', th⟩, hst, rfl⟩ := hs2
    refine cohM_store ?_ hst
    simp only [mth, nWords, List.map, Acc.size, List.sum_cons, List.sum_nil]
    intro i m hm hi
    have hr : List.range (1 + 0) = [0] := rfl
    simp only [hr, List.foldl] at hm
    rw [Array.getElem?_push] at hm
    split at hm
    · rename_i he
      cases hm
      simp [offs, he]
    · have hlt := (Array.getElem?_eq_some_iff.mp hm).1
      have := hc i m hm hi
      show i ≤ (if m.loc.label = lbl ∧ m.loc.offset < 1 + 0 then s.mem.size + m.loc.offset else s.vs.coh m.loc)
      by_cases hl : m.loc.label = lbl ∧ m.loc.offset < 1 + 0
      · simp only [hl]; exact Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_add_right _ _)
      · simp only [hl, ite_false]; exact this

/-! ## One step of main -/

/-- **One thread step of main keeps `CohC` and `PB`.** -/
theorem cohC_tstep {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh}
    (hg : g.p = wakeSrc) (hi : TInv mem.size th) (hc : CohC mem th)
    (h : (mem', pairs', th') ∈ tstep g mem pairs th) : CohC mem' th' ∧ PB th' := by
  obtain ⟨hm, -, -, -, hz, -⟩ := hi
  rcases hm with ht | ht | ht | ht | ht | ht
  · obtain ⟨d, hd, hb⟩ := main_decl
    rw [← hg] at hd
    simp [tstep, ht, mStart, enter, hd] at h
    cases hme : evalAt th.env (.var "me") with
    | none => simp [hme, ol] at h
    | some r =>
      obtain ⟨t, ws⟩ := r
      simp only [hme, ol, Option.bind_some, Function.comp, Option.map_some, Option.toList_some,
        List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hc, fun h => by simp [hb, mBody, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h⟩
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "z" (.zero .int) mZ) rfl] at h
    have hcl : close th.σs Ty.int = .int := rfl
    simp [evalOp, ol, stOf, hcl, zeroWords] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hc, fun h => by simp [withS, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h⟩
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "o" (.new (.var "z")) mO) rfl] at h
    have hzt := hz ht
    cases hzl : lookupE th.env "z" with
    | none => simp [hzl] at hzt
    | some r =>
      obtain ⟨t, ws⟩ := r
      simp only [hzl, Option.map_some, Option.some.injEq] at hzt
      subst hzt
      simp only [evalOp, evalAt, hzl, accs, List.map_map, List.mem_map, Function.comp] at h
      obtain ⟨⟨s', pw⟩, ha, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl, rfl⟩ := he'
      exact ⟨cohM_alloc (s := stOf mem pairs th) hc ha, fun h => by simp [withS, mO, mC, spawnTerm, WakePreA.spawnTerm] at h⟩
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "c" (.publish (.var "o")) mC) rfl] at h
    obtain ⟨⟨s', t, ws⟩, hr, rfl, rfl, rfl⟩ := List.mem_map.mp h
    obtain ⟨rfl, -⟩ := publish_res hr
    exact ⟨hc, fun h => by simp [withS, mC, spawnTerm, WakePreA.spawnTerm] at h⟩
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm) rfl] at h
    cases hc' : evalAt th.env (.var "c") with
    | none => simp [evalOp, ol, hc'] at h
    | some r =>
    cases hm : evalAt th.env (.var "me") with
    | none => simp [evalOp, ol, hc', hm] at h
    | some r' =>
      obtain ⟨t, ws⟩ := r
      obtain ⟨t', ws'⟩ := r'
      simp [evalOp, ol, hc', hm, stOf, withS] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hc, fun _ => ⟨t, ws, t', ws', ?_, ?_, ?_⟩⟩
      · simpa [withS, lookupE, evalAt] using hc'
      · simpa [withS, lookupE, evalAt] using hm
      · simp [lookupE]
  · rw [TermLocal.tstep_let_gen
      (ht.trans rfl : th.term = .let_ "t" (.spawn "worker" (.var "p") (.prod (.ptr .pub .int) .tid) []) mTail) rfl] at h
    simp [evalOp] at h

/-! ## Along source runs -/

/-- **One source step keeps `VPreC`** (with `VPre`, for main's term). -/
theorem vpreC_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (wakeS arch).step i s es s')
    (hv : VPre s) (hc : VPreC s) : VPreC s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have hsz := stepBy_size hs
    have h1 : s.ths.size = 1 := hsz ▸ h1'
    obtain ⟨th0, h0, hi⟩ := hv h1
    obtain ⟨th0', h0', hci⟩ := hc h1
    rw [h0] at h0'; cases h0'
    rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
    · unfold TermRun.threadSteps at hm
      split at hm
      · simp at hm
      · rename_i th hth
        obtain rfl := idx0 h1 hth
        rw [h0] at hth; cases hth
        obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
        exact ⟨th', getElem?_set!_self h0 _, cohC_tstep rfl hi hci.1 hr⟩
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise
      rw [h0]
      refine ⟨_, getElem?_set!_self h0 _, ?_, hci.2⟩
      intro k m hm hk
      simp only [List.mem_append, List.mem_singleton, not_or] at hk
      rw [Array.getElem?_push] at hm
      split at hm
      · exact absurd ‹_› hk.2
      · exact hci.1 k m hm hk.1
  · have := (spawnBy_size hs).1
    obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, -⟩ := hs
    have := (Array.getElem?_eq_some_iff.mp hth).1
    omega
  · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -, -, -, -, rfl⟩ := hs
    have h1 : s.ths.size = 1 := by rwa [TermExtStep.wake_size, TermExtStep.extCfg_size] at h1'
    obtain ⟨th0, h0, hi⟩ := hv h1
    obtain rfl := idx0 h1 hth
    rw [h0] at hth; cases hth
    exact (not_ext hi.1 hterm).elim

theorem vpreC_init {arch : Arch} {s : Cfg} (h : (wakeS arch).init s) : VPreC s := by
  have h' : s = WakeT1.tidStartT 2 := by
    change WakeT1.progInitT wakeSrc 2 s at h
    rw [WakeT1.wake_start] at h
    exact h
  subst h'
  intro _
  refine ⟨_, rfl, fun k m hm _ => ?_, fun h => ?_⟩
  · simp [WakeT1.tidStartT] at hm
  · simp [WakeT1.tidStartT, spawnTerm, WakePreA.spawnTerm] at h

/-- **`VPreC` along source runs** (with `VPre` at the start). -/
theorem vpreC_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (wakeS arch).Run s tr s') (hv : VPre s)
    (hc : VPreC s) : VPreC s' := by
  induction h with
  | refl => exact hc
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vpre_step hs hv) (vpreC_step hs hv hc)

open Spike.Lib.WakePreTi (Pre1T) in
/-- **`Pre1T` with `VPreC`** (generic in the entry `E` and the relation,
over a relation that already carries `VPre`, e.g. `WakeSpawnLt.pre1T_vpre`'s). -/
theorem pre1T_vpreC {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
    {R1 : WakeA64.Cfg → TermRun.Cfg → Prop} {Ab Ac : Kraken.Promising.AArch64.State → Prop}
    (O : Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPre s) Ab Ac) :
    Pre1T arch Λ B asm E (fun d s => (R1 d s ∧ VPre s) ∧ VPreC s) Ab Ac :=
  Spike.Lib.WakePreInv.Pre1T.inv O (fun _ s => VPreC s) (fun _ _ _ hi _ => vpreC_init hi)
    (fun _ _ _ _ _ _ hR hc _ _ hr _ => vpreC_run hr hR.2 hc)

/-! ## At the spawn -/

/-- **Coherence at the spawn** (`SpawnPre.scov0`/`scov1`'s form, at every
location): at main's spawn of `s` (one thread `th0`, promise-free, with
`VPreC`), every message of the spawned configuration is at most the
coherence of both its threads at its location. -/
theorem scov_spawn {s : Cfg} {th0 : TTh} {x f : String} {e : Expr} {ts : List Ty} {T : Ty} {ws : List Word}
    (hc : VPreC s) (hs : s.ths = #[th0]) (hp : th0.promises = []) :
    (∀ k m, (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).mem[k]? = some m →
      k ≤ (TermSpawnStep.spawnPar s 0 th0 x e).vs.coh m.loc) ∧
    (∀ k m, (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).mem[k]? = some m →
      k ≤ (TermSpawnStep.spawnKid s 0 th0 f ts T ws).vs.coh m.loc) := by
  obtain ⟨th, h0, hci⟩ := hc (by rw [hs]; rfl)
  obtain rfl : th0 = th := by rw [hs] at h0; simpa using h0
  have hk : ∀ k m, s.mem[k]? = some m → k ≤ th0.vs.coh m.loc := fun k m hm =>
    hci.1 k m hm (by rw [hp]; exact List.not_mem_nil)
  exact ⟨fun k m hm => hk k m hm, fun k m hm => hk k m hm⟩

/-- `scov_spawn` at `SpawnPre.ths`'s names: `s' = spawnCfg …` with threads
`#[s0, s1]` (the frozen-set antecedent of `scov0`/`scov1` dropped). -/
theorem scov_of {s s' : Cfg} {th0 s0 s1 : TTh} {x f : String} {e : Expr} {ts : List Ty} {T : Ty}
    {ws : List Word} (hc : VPreC s) (hs : s.ths = #[th0]) (hp : th0.promises = [])
    (hs' : s' = TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws) (h2 : s'.ths = #[s0, s1]) :
    (∀ k m, s'.mem[k]? = some m → k ≤ s0.vs.coh m.loc) ∧ (∀ k m, s'.mem[k]? = some m → k ≤ s1.vs.coh m.loc) := by
  subst hs'
  have h2' : (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).ths =
      #[TermSpawnStep.spawnPar s 0 th0 x e, TermSpawnStep.spawnKid s 0 th0 f ts T ws] := by
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hs]
  have hq := h2.symm.trans h2'
  have h0' : (#[s0, s1] : Array TTh)[0]? = some s0 := rfl
  have h1' : (#[s0, s1] : Array TTh)[1]? = some s1 := rfl
  rw [hq] at h0' h1'
  obtain rfl : TermSpawnStep.spawnPar s 0 th0 x e = s0 := Option.some.inj h0'
  obtain rfl : TermSpawnStep.spawnKid s 0 th0 f ts T ws = s1 := Option.some.inj h1'
  exact scov_spawn hc hs hp

/-- info: 'Spike.Lib.SpawnCohSteps.vpreC_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vpreC_run

/-- info: 'Spike.Lib.SpawnCohSteps.pre1T_vpreC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_vpreC

/-- info: 'Spike.Lib.SpawnCohSteps.scov_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scov_of

end Spike.Lib.SpawnCohSteps
