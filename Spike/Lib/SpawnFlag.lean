/-
**The flag's last write at wake's spawn, from the start** (`vflag_spawn`),
and its target image (`flag_of_inv1`): the facts behind
`WakeSpawn.SpawnPre.flag`/`flagLast`.

Before the spawn, wake's source has one thread, `main`. `zero` binds `z` to
the word `0`; `new` of it pushes the cell's `undef` message at `⟨l, 0⟩` and
then stores `0` there. That store appends: a fulfilled promise would have to
lie above the coherence `new` raised to its `undef` message, the top of the
memory. From then on every later message at `⟨l, 0⟩` is one of `main`'s
promises (only promise steps grow the memory), and `publish` binds `c` to
`o`'s word (`FlagMem`, `FlagC`). At the spawn `main` has no promises, so
the stored `0` is the latest source message at `⟨l, 0⟩`, with the `undef`
message before it (`vflag_spawn`). Through `Inv1` (no promise, so the
memory relation's latest message is the target's last write) it is a `0` at
the target's last write of the flag's word, which is not the initial write
(`ts_first`: an earlier source message has the same location), and no later
target message is to that word (`flag_of_inv1`).

- `FlagMem`, `FlagC`, `VFlag`: the invariant (vacuous once there are two
  threads).
- `alloc_flag`: `new` of the word `0` establishes `FlagMem` at its label.
- `vflag_init`, `vflag_step`, `vflag_run`: it holds along source runs (with
  `VPre`, for `main`'s term).
- `pre1T_vflag`: any `Pre1T` whose relation implies `VPre`, strengthened by
  `VFlag`.
- `vflag_spawn`: at `spawnTerm` with `main` promise-free, `c`'s label's
  latest message (`SLatestP` with no promise) holds `0`, after an earlier one.
- `flag_of_inv1`, `flag_at`: the target's last write of the flag's word
  reads `0` and is the last message there (`SpawnPre.flag`/`flagLast`).
-/
import Spike.Lib.SpawnViewLtSteps
import Spike.Lib.WakePreInv

namespace Spike.Lib.SpawnFlag

open CoreLang CoreTerm TermRun
open WeakMem (VState Address Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeA64 (wakeS)
open Spike.Lib.WakeM0 (mTail)
open Spike.Lib.SpawnViewLtSteps
open Spike.Lib.WorkerSrcStep (getElem?_set!_self)

/-! ## The invariant -/

/-- **The flag cell at label `l`**: an earlier message at `⟨l, 0⟩`, then a
message there holding `0`, after which every message there is among the
promises `P`. -/
def FlagMem (mem : WeakMem.Memory) (P : List Ts) (l : WeakMem.AllocLabel) : Prop :=
  ∃ i j, i < j ∧ (∃ m, mem[i]? = some m ∧ m.loc = ⟨l, 0⟩) ∧
    (∃ m, mem[j]? = some m ∧ m.loc = ⟨l, 0⟩ ∧ m.val = .num 0) ∧
    ∀ (k : Nat) m, j < k → mem[k]? = some m → m.loc = ⟨l, 0⟩ → k ∈ P

/-- **main's flag facts**: `z` is the word `0` at `new`; the label of `o`'s
word (at `publish`) and of `c`'s word (from then on) has `FlagMem`. -/
def FlagC (mem : WeakMem.Memory) (th : TTh) : Prop :=
  (th.term = mZ → ∃ t, lookupE th.env "z" = some (t, [cst (.num 0)])) ∧
    ∀ l, (th.term = mO ∧ (∃ t, lookupE th.env "o" = some (t, [cst (.loc ⟨l, 0⟩ 0)])) ∨
        (th.term = mC ∨ th.term = spawnTerm) ∧ ∃ t, lookupE th.env "c" = some (t, [cst (.loc ⟨l, 0⟩ 0)])) →
      FlagMem mem th.promises l

/-- **The source flag invariant before the spawn**: with one thread, it has
`FlagC`. -/
def VFlag (s : Cfg) : Prop := s.ths.size = 1 → ∃ th0, s.ths[0]? = some th0 ∧ FlagC s.mem th0

/-- A promise step keeps `FlagMem` (its message is a promise). -/
theorem FlagMem.push {mem : WeakMem.Memory} {P : List Ts} {l : WeakMem.AllocLabel} (h : FlagMem mem P l)
    (m0 : WeakMem.Msg) : FlagMem (mem.push m0) (P ++ [mem.size]) l := by
  obtain ⟨i, j, hij, ⟨mi, hi, hil⟩, ⟨mj, hj, hjl, hjv⟩, hk⟩ := h
  refine ⟨i, j, hij, ⟨mi, ?_, hil⟩, ⟨mj, ?_, hjl, hjv⟩, fun k m hjk hm hl => ?_⟩
  · rw [TermMem.push_lt (TermLiveProps.lt_of_get hi)]; exact hi
  · rw [TermMem.push_lt (TermLiveProps.lt_of_get hj)]; exact hj
  · rw [Array.getElem?_push] at hm
    split at hm
    · rename_i he; subst he; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (hk k m hjk hm hl)

/-! ## `new` -/

/-- **`new` of the word `0`**: its store appends after the `undef` message
(a fulfilled promise would lie above the raised coherence, the top of the
memory), so its label has `FlagMem`. -/
theorem alloc_flag {k : Promises.Knobs} {arch : Arch} {lbl : WeakMem.AllocLabel} {s s' : St} {pw : Word}
    (h : (s', pw) ∈ alloc k arch lbl [.one] [cst (.num 0)] s) :
    FlagMem s'.mem s'.promises lbl ∧ pw = cst (.loc ⟨lbl, 0⟩ 0) := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at hs2
  obtain ⟨⟨mem', th⟩, hst, rfl⟩ := hs2
  refine ⟨?_, rfl⟩
  have hr : List.range (nWords [Acc.one]) = [0] := rfl
  simp only [hr, List.foldl] at hst
  obtain ⟨t, hc, -, -, -⟩ := TermStep.stepStore_casesC hst
  rcases hc with ⟨rfl, -, hp⟩ | ⟨rfl, -, -, hlt, m, hm, -⟩
  · have h1 : ∀ (a : WeakMem.Memory) (x y : WeakMem.Msg), ((a.push x).push y)[a.size]? = some x := by
      intro a x y; rw [TermMem.push_lt (by simp), Array.getElem?_push_size]
    have h2 : ∀ (a : WeakMem.Memory) (x y : WeakMem.Msg), ((a.push x).push y)[a.size + 1]? = some y := by
      intro a x y; rw [← Array.size_push (xs := a) (v := x), Array.getElem?_push_size]
    refine ⟨s.mem.size, s.mem.size + 1, Nat.lt_succ_self _, ⟨_, h1 _ _ _, rfl⟩, ⟨_, h2 _ _ _, rfl, ?_⟩, ?_⟩
    · simp [TermMem.exprVal, dataE, cst, Promises.TVal.mk0]
    · intro k m hk hm
      have := TermLiveProps.lt_of_get hm
      simp only [Array.size_push] at this
      omega
  · exfalso
    have := TermLiveProps.lt_of_get hm
    simp only [mth, offs, nWords, Array.size_push] at hlt this
    simp only [List.map, List.sum_cons, List.sum_nil, Acc.size] at hlt
    simp at hlt
    simp only [WeakMem.Ts] at *
    omega

/-! ## One step of main -/

/-- **One thread step of main keeps `FlagC`.** -/
theorem flagC_tstep {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh}
    (hg : g.p = wakeSrc) (hi : TInv mem.size th) (hf : FlagC mem th)
    (h : (mem', pairs', th') ∈ tstep g mem pairs th) : FlagC mem' th' := by
  obtain ⟨hm, -, -, -, hz, -⟩ := hi
  obtain ⟨hfz, hfl⟩ := hf
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
      refine ⟨fun h => ?_, fun l h => ?_⟩
      · simp [hb, mBody, mZ] at h
      · simp [hb, mBody, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "z" (.zero .int) mZ) rfl] at h
    have hcl : close th.σs Ty.int = .int := rfl
    simp [evalOp, ol, stOf, hcl, zeroWords] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨fun _ => ⟨.int, by simp [lookupE, withS]⟩, fun l h => ?_⟩
    simp [withS, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "o" (.new (.var "z")) mO) rfl] at h
    have hzt := hz ht
    obtain ⟨t0, hz0⟩ := hfz ht
    rw [hz0] at hzt
    simp only [Option.map_some, Option.some.injEq] at hzt
    subst hzt
    simp only [evalOp, evalAt, hz0, accs, List.map_map, List.mem_map, Function.comp] at h
    obtain ⟨⟨s', pw⟩, ha, he'⟩ := h
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    obtain ⟨hfm, rfl⟩ := alloc_flag ha
    refine ⟨fun h => ?_, fun l h => ?_⟩
    · simp [withS, mO, mZ] at h
    · rcases h with ⟨-, t, hl⟩ | ⟨h, -⟩
      · simp [withS, lookupE, cst, Promises.TVal.mk0] at hl
        obtain ⟨-, rfl⟩ := hl
        exact hfm
      · simp [withS, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "c" (.publish (.var "o")) mC) rfl] at h
    obtain ⟨⟨s', t, ws⟩, hr, rfl, rfl, rfl⟩ := List.mem_map.mp h
    obtain ⟨rfl, t0, ho⟩ := publish_res hr
    refine ⟨fun h => ?_, fun l h => ?_⟩
    · simp [withS, mC, mZ] at h
    · rcases h with ⟨h, -⟩ | ⟨-, t1, hl⟩
      · simp [withS, mC, mO] at h
      · simp only [withS, lookupE, List.find?_cons_of_pos, beq_self_eq_true, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        exact hfl l (Or.inl ⟨ht, t0, ho⟩)
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
      refine ⟨fun h => ?_, fun l h => ?_⟩
      · simp [spawnTerm, WakePreA.spawnTerm, mZ] at h
      · rcases h with ⟨h, -⟩ | ⟨-, t1, hl⟩
        · simp [spawnTerm, WakePreA.spawnTerm, mO] at h
        · have hl' : lookupE th.env "c" = some (t1, [cst (.loc ⟨l, 0⟩ 0)]) := by simpa [lookupE] using hl
          exact hfl l (Or.inr ⟨Or.inl ht, t1, hl'⟩)
  · rw [TermLocal.tstep_let_gen
      (ht.trans rfl : th.term = .let_ "t" (.spawn "worker" (.var "p") (.prod (.ptr .pub .int) .tid) []) mTail) rfl] at h
    simp [evalOp] at h

/-! ## Along source runs -/

/-- **One source step keeps `VFlag`** (with `VPre`, for main's term). -/
theorem vflag_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (wakeS arch).step i s es s')
    (hv : VPre s) (hf : VFlag s) : VFlag s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have hsz := stepBy_size hs
    have h1 : s.ths.size = 1 := hsz ▸ h1'
    obtain ⟨th0, h0, hi⟩ := hv h1
    obtain ⟨th0', h0', hfi⟩ := hf h1
    rw [h0] at h0'; cases h0'
    rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
    · unfold TermRun.threadSteps at hm
      split at hm
      · simp at hm
      · rename_i th hth
        obtain rfl := idx0 h1 hth
        rw [h0] at hth; cases hth
        obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
        exact ⟨th', getElem?_set!_self h0 _, flagC_tstep rfl hi hfi hr⟩
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise
      rw [h0]
      refine ⟨_, getElem?_set!_self h0 _, fun hz => hfi.1 hz, fun l hl => (hfi.2 l hl).push _⟩
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

theorem vflag_init {arch : Arch} {s : Cfg} (h : (wakeS arch).init s) : VFlag s := by
  have h' : s = WakeT1.tidStartT 2 := by
    change WakeT1.progInitT wakeSrc 2 s at h
    rw [WakeT1.wake_start] at h
    exact h
  subst h'
  intro _
  refine ⟨_, rfl, fun h => ?_, fun l h => ?_⟩
  · simp [WakeT1.tidStartT, mZ] at h
  · simp [WakeT1.tidStartT, mO, mC, spawnTerm, WakePreA.spawnTerm] at h

/-- **`VFlag` along source runs** (with `VPre` at the start). -/
theorem vflag_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (wakeS arch).Run s tr s') (hv : VPre s)
    (hf : VFlag s) : VFlag s' := by
  induction h with
  | refl => exact hf
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vpre_step hs hv) (vflag_step hs hv hf)

open Spike.Lib.WakePreTi (Pre1T) in
/-- **`Pre1T` with `VFlag`** (generic in the entry `E` and in a relation
`R1` that implies `VPre`, e.g. `((… ∧ VPre) ∧ VPreC)`). -/
theorem pre1T_vflag {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
    {R1 : WakeA64.Cfg → TermRun.Cfg → Prop} {Ab Ac : Kraken.Promising.AArch64.State → Prop}
    (O : Pre1T arch Λ B asm E R1 Ab Ac) (hv : ∀ d s, R1 d s → VPre s) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VFlag s) Ab Ac :=
  Spike.Lib.WakePreInv.Pre1T.inv O (fun _ s => VFlag s) (fun _ _ _ hi _ => vflag_init hi)
    (fun _ _ _ _ _ _ hR hf _ _ hr _ => vflag_run hr (hv _ _ hR) hf)

/-! ## At the spawn -/

/-- **The flag's latest source message at the spawn**: at main's spawn of
`s` (one thread `th0` at `spawnTerm`, promise-free, with `VFlag`), for `c`'s
label `l`, the latest message at `⟨l, 0⟩` (no promise) holds `0`, and an
earlier message is there too. -/
theorem vflag_spawn {s : Cfg} {th0 : TTh} {l : WeakMem.AllocLabel} {T : Ty} (hf : VFlag s)
    (hs : s.ths = #[th0]) (ht : th0.term = spawnTerm) (hp : th0.promises = [])
    (hc : evalAt th0.env (.var "c") = some (T, [cst (.loc ⟨l, 0⟩ 0)])) :
    ∃ i j, i < j ∧ (∃ m, s.mem[i]? = some m ∧ m.loc = ⟨l, 0⟩) ∧ SLatestP s.mem [] ⟨l, 0⟩ j ∧
      ∃ m, s.mem[j]? = some m ∧ m.val = .num 0 := by
  obtain ⟨th, h0, hfl⟩ := hf (by rw [hs]; rfl)
  obtain rfl : th0 = th := by rw [hs] at h0; simpa using h0
  obtain ⟨i, j, hij, hi, ⟨m, hm, hml, hmv⟩, hk⟩ := hfl.2 l (Or.inr ⟨Or.inr ht, T, hc⟩)
  rw [hp] at hk
  exact ⟨i, j, hij, hi, ⟨⟨m, hm, hml, List.not_mem_nil⟩, hk⟩, m, hm, hmv⟩

/-- The spawn keeps the source memory. -/
theorem spawnCfg_mem {s : Cfg} {i : Nat} {th0 : TTh} {x f : String} {e : Expr} {ts : List Ty} {T : Ty}
    {ws : List Word} : (TermSpawnStep.spawnCfg s i th0 x e f ts T ws).mem = s.mem := rfl

open Kraken.Promising in
/-- **The flag at the target** (`SpawnPre.flag`/`flagLast`'s form): under
`Inv1` with no target promise, a source latest message (no source promise)
at `⟨l, 0⟩` holding `0`, after an earlier message there, is a `0` at the
target's last write of the word at `l`'s address `A`, and no later target
message is to that word. -/
theorem flag_of_inv1 {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}
    {l : WeakMem.AllocLabel} {A i j : Nat} (hI : Inv1 Λ lbl lsize ts t tm sm) (hp : t.prom = []) (hwf : Λ.WF)
    (hA : lbl l = some A) (hij : i < j) (hi : ∃ m, sm[i]? = some m ∧ m.loc = ⟨l, 0⟩)
    (hj : SLatestP sm [] ⟨l, 0⟩ j) (hv : ∃ m, sm[j]? = some m ∧ m.val = .num 0) :
    ∃ k', tm.read? (wordLoc A) k' = some 0 ∧ ∀ k w', k' < k → tm.get? k = some w' → w'.loc ≠ wordLoc A := by
  have ha : wordAddr lbl ⟨l, 0⟩ = some A := by simp [wordAddr, hA]
  have hk : TLatestP tm ([] ++ t.prom) A (tm.lastWrite (wordLoc A)) := by
    rw [hp]
    refine ⟨?_, fun k'' w hlt hg hl => absurd hl (Memory.not_write_of_lastWrite_lt tm _ hlt hg)⟩
    by_cases h0 : tm.lastWrite (wordLoc A) = 0
    · exact Or.inl h0
    · obtain ⟨w, hg, hl⟩ := Memory.get?_lastWriteBelow tm (wordLoc A) tm.last h0
      exact Or.inr ⟨w, hg, hl, List.not_mem_nil⟩
  obtain ⟨hts, m, v, hm, hw, hrep⟩ := hI.mem.latestP hwf hI.narrow ha hj hk
  obtain ⟨m', hm', hv'⟩ := hv
  rw [hm] at hm'; cases hm'
  rw [hv'] at hrep
  obtain ⟨-, rfl⟩ := hrep
  have hpos : 0 < tm.lastWrite (wordLoc A) := by
    rcases Nat.eq_zero_or_pos (tm.lastWrite (wordLoc A)) with h0 | h0
    · exfalso
      rw [h0] at hts
      obtain ⟨mi, hmi, hil⟩ := hi
      obtain ⟨⟨m2, hm2, hl2, -⟩, -⟩ := hj
      rw [hm] at hm2; cases hm2
      exact hI.mem.ts_first j m hm hts i mi hij hmi (hil.trans hl2.symm)
    · exact h0
  obtain ⟨w, hg, hl, h0⟩ := MemRel.wordAt_msg hI.narrow hpos hw
  refine ⟨_, ?_, fun k w' hlt hg' => Memory.not_write_of_lastWrite_lt tm _ hlt hg'⟩
  have hw0 : w.val = 0 := BitVec.eq_of_toNat_eq (by simpa using h0.symm)
  simp [Memory.read?, Nat.pos_iff_ne_zero.mp hpos, hg, hl, hw0]

open Kraken.Promising in
/-- `flag_of_inv1` at the instance's flag word `wordLoc ((lbl l).getD 0 + 8 * 0)`. -/
theorem flag_at {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}
    {l : WeakMem.AllocLabel} {A i j : Nat} (hI : Inv1 Λ lbl lsize ts t tm sm) (hp : t.prom = []) (hwf : Λ.WF)
    (hA : lbl l = some A) (hij : i < j) (hi : ∃ m, sm[i]? = some m ∧ m.loc = ⟨l, 0⟩)
    (hj : SLatestP sm [] ⟨l, 0⟩ j) (hv : ∃ m, sm[j]? = some m ∧ m.val = .num 0) :
    ∃ k', tm.read? (wordLoc ((lbl l).getD 0 + 8 * 0)) k' = some 0 ∧
      ∀ k w', k' < k → tm.get? k = some w' → w'.loc ≠ wordLoc ((lbl l).getD 0 + 8 * 0) := by
  have he : (lbl l).getD 0 + 8 * 0 = A := by simp [hA]
  rw [he]
  exact flag_of_inv1 hI hp hwf hA hij hi hj hv

/-- info: 'Spike.Lib.SpawnFlag.vflag_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vflag_run

/-- info: 'Spike.Lib.SpawnFlag.pre1T_vflag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_vflag

/-- info: 'Spike.Lib.SpawnFlag.vflag_spawn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms vflag_spawn

/-- info: 'Spike.Lib.SpawnFlag.flag_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flag_at

end Spike.Lib.SpawnFlag
