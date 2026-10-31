/-
**Strict view bounds at wake's spawn, from the start** (`vpre_spawn`), the
spawn step as a source run (`run_spawnCfg`), and main's source fields past
the spawn (`src_fields`).

Before the spawn, wake's source has one thread, `main`, at one of six terms
(`MainPre`: the entry tail call, `main`'s body, and its continuations after
`z`, `o`, `c`, `p`). Along that prefix, every view of `main`'s thread and
every word of its environment is at most the memory size minus one
(`TInv`): the start has empty memory and zero views; `zero` and `pair` keep
the thread's state; `new` pushes its cell's `undef` messages and stores at
them (coherence, `vWr` move to the new timestamps); `publish` (`dmb st`)
raises `vRelSt` to at most `vWr`; the tail call into `main` keeps the views;
promise steps only grow memory. From `new` on the memory is nonempty, so at
the spawn the bounds are strict (`SpawnViewLt.SpawnVLt`), as
`SpawnViewLt.hview_of_spawnCfg` needs.

- `MainPre`, `TInv`, `VPre`: the invariant (vacuous once there are two
  threads).
- `vpre_init`, `vpre_step`, `vpre_run`: it holds along source runs.
- `vpre_spawn`: at `spawnTerm`, `SpawnVLt` and `EnvLt` below the memory
  size.
- `run_spawnCfg`: main's spawn is a source run with the empty trace.
- `src_fields`: at the spawn's parent `Ctl.of (spawnPar …)`, `c`'s binding,
  its word's representation at a label placed at `A`.
-/
import Spike.Lib.SpawnViewLt
import Spike.Lib.WakeM0
import Spike.Lib.WakePreA

namespace Spike.Lib.SpawnViewLtSteps

open CoreLang CoreTerm TermRun
open WeakMem (VState Address Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.WakeT1 (wakeSrc tidStartT wake_start)
open Spike.Lib.WakeA64 (wakeS)
open Spike.Lib.WakeM0 (mTail)
open Spike.Lib.SpawnViewLt (SpawnVLt)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self)

/-! ## main's terms before the spawn -/

/-- **main's term at the `spawn`**: `WakePreA.spawnTerm`,
`let t = spawn worker p in mTail`. -/
abbrev spawnTerm : Expr := WakePreA.spawnTerm

theorem spawnTerm_eq :
    spawnTerm = .let_ "t" (.spawn "worker" (.var "p") (.prod (.ptr .pub .int) .tid) []) mTail := rfl

/-- main's body after `c`. -/
def mC : Expr := .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm

/-- main's body after `o`. -/
def mO : Expr := .let_ "c" (.publish (.var "o")) mC

/-- main's body after `z`. -/
def mZ : Expr := .let_ "o" (.new (.var "z") (some .int)) mO

/-- main's body. -/
def mBody : Expr := .let_ "z" (.zero .int) mZ

/-- The start's term: the tail call into `main`. -/
def mStart : Expr := .tail "main" [] (.var "me")

theorem main_find : (wakeSrc.find? (·.name == "main")).map (·.body) = some mBody := rfl

/-- **The terms main is at before the spawn.** -/
def MainPre (e : Expr) : Prop :=
  e = mStart ∨ e = mBody ∨ e = mZ ∨ e = mO ∨ e = mC ∨ e = spawnTerm

/-! ## The invariant -/

/-- Strict bounds on the environment's words (the form `hview_of_spawnCfg`
takes). -/
def EnvLt (th : TTh) (n : Nat) : Prop := ∀ p ∈ th.env, ∀ w ∈ p.2.2, w.view < n ∧ w.rts < n

/-- The thread's scalar views and coherence at most `m`. -/
def VB (vs : VState) (m : Nat) : Prop :=
  vs.vRd ≤ m ∧ vs.vWr ≤ m ∧ vs.vCtrl ≤ m ∧ vs.vPreBase ≤ m ∧ vs.vRelSt ≤ m ∧ ∀ a, vs.coh a ≤ m

/-- The environment's words' views and read timestamps at most `m`. -/
def EnvB (env : Env) (m : Nat) : Prop := ∀ p ∈ env, ∀ w ∈ p.2.2, w.view ≤ m ∧ w.rts ≤ m

/-- **main's thread before the spawn, at memory size `n`**: at a `MainPre`
term with no stack, views and environment words at most `n - 1`, `z` an
`Int` at `new`, memory nonempty from `new` on. -/
def TInv (n : Nat) (th : TTh) : Prop :=
  MainPre th.term ∧ th.stack = [] ∧ VB th.vs (n - 1) ∧ EnvB th.env (n - 1) ∧
    (th.term = mZ → (lookupE th.env "z").map (·.1) = some .int) ∧
    (th.term = mO ∨ th.term = mC ∨ th.term = spawnTerm → 0 < n)

/-- **The source invariant before the spawn**: with one thread, it is
`main` and `TInv`. -/
def VPre (s : Cfg) : Prop := s.ths.size = 1 → ∃ th0, s.ths[0]? = some th0 ∧ TInv s.mem.size th0

theorem VB.mono {vs : VState} {m m' : Nat} (h : VB vs m) (hm : m ≤ m') : VB vs m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.le_trans h1 hm, Nat.le_trans h2 hm, Nat.le_trans h3 hm, Nat.le_trans h4 hm, Nat.le_trans h5 hm,
    fun a => Nat.le_trans (h6 a) hm⟩

theorem EnvB.mono {env : Env} {m m' : Nat} (h : EnvB env m) (hm : m ≤ m') : EnvB env m' :=
  fun p hp w hw => (h p hp w hw).imp (Nat.le_trans · hm) (Nat.le_trans · hm)

theorem TInv.mono {n n' : Nat} {th : TTh} (h : TInv n th) (hn : n ≤ n') : TInv n' th := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3.mono (by omega), h4.mono (by omega), h5, fun h => by have := h6 h; omega⟩

theorem EnvB.cons {env : Env} {m : Nat} (h : EnvB env m) {x : String} {t : Ty} {ws : List Word}
    (hw : ∀ w ∈ ws, w.view ≤ m ∧ w.rts ≤ m) : EnvB ((x, t, ws) :: env) m := by
  intro p hp w hw'
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hw w hw'
  · exact h p hp w hw'

theorem EnvB.lookup {env : Env} {m : Nat} (h : EnvB env m) {x : String} {t : Ty} {ws : List Word}
    (hl : lookupE env x = some (t, ws)) : ∀ w ∈ ws, w.view ≤ m ∧ w.rts ≤ m :=
  fun w hw => h _ (TermNoFul.lookupE_mem hl) w hw

theorem cst_b (v : WeakMem.Val) (m : Nat) : ∀ w ∈ [cst v], w.view ≤ m ∧ w.rts ≤ m := by
  intro w hw
  rw [List.mem_singleton] at hw
  subst hw
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-! ## One step of main -/

/-- A store keeps the read, control and pre-base views. -/
theorem stepStore_vs {k : Promises.Knobs} {arch : Arch} {mem mem' : WeakMem.Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    th'.vs.vRd = th.vs.vRd ∧ th'.vs.vCtrl = th.vs.vCtrl ∧ th'.vs.vPreBase = th.vs.vPreBase := by
  simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
  rcases h with h | ⟨t, -, hf⟩
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · split at hf
    · simp at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, -, rfl⟩ := hf
      exact ⟨rfl, rfl, rfl⟩

/-- **`new` of one word**: memory grows, the views stay at most its size
minus one, the pointer word is a constant. -/
theorem alloc_vb {k : Promises.Knobs} {arch : Arch} {lbl : WeakMem.AllocLabel} {ws : List Word} {s s' : St}
    {pw : Word} (hv : VB s.vs (s.mem.size - 1)) (h : (s', pw) ∈ alloc k arch lbl [.one] ws s) :
    s.mem.size < s'.mem.size ∧ VB s'.vs (s'.mem.size - 1) ∧ pw = cst (.loc ⟨lbl, 0⟩ 0) := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  cases ws with
  | nil => simp [storeUnits] at hs2
  | cons w ws =>
    simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at hs2
    obtain ⟨⟨mem', th⟩, hst, rfl⟩ := hs2
    dsimp only
    obtain ⟨t, hc, hcoh, hrel, hwr⟩ := TermStep.stepStore_casesC hst
    obtain ⟨e1, e2, e3⟩ := stepStore_vs hst
    have hsz := TermMem.fold_size (fun j => (⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩ : WeakMem.Msg)) (nWords [.one]) s.mem
    have hn : nWords [Acc.one] = 1 := rfl
    rw [hn] at hsz
    have ht : t ≤ mem'.size - 1 ∧ s.mem.size + 1 ≤ mem'.size := by
      rcases hc with ⟨rfl, rfl, -⟩ | ⟨rfl, -, -, -, m, hm, -⟩
      · simp only [Array.size_push, hn] at hsz ⊢
        omega
      · have := TermLiveProps.lt_of_get hm
        simp only [hn] at hsz this ⊢
        omega
    refine ⟨by omega, ?_, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
    simp only [mth] at hcoh hrel hwr e1 e2 e3
    simp only [hn] at hcoh hrel hwr
    simp only [VB, e1, e2, e3, hrel, hwr, hcoh]
    simp only [WeakMem.Ts] at *
    refine ⟨by omega, by omega, by omega, by omega, by omega, fun b => ?_⟩
    split
    · omega
    · split
      · rename_i hb; have h0 : b.offset = 0 := Nat.lt_one_iff.mp hb.2
        rw [h0, Nat.add_zero]; exact Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ht.2)
      · have := h6 b; omega

theorem main_decl : ∃ d, wakeSrc.find? (·.name == "main") = some d ∧ d.body = mBody := by
  have := main_find
  rw [Option.map_eq_some_iff] at this
  exact this

/-- A `publish`'s result: the `dmb st` state, the operand's words. -/
theorem publish_res {g : G} {env : Env} {σs : List Ty} {s s' : St} {a : At} {t : Ty} {ws : List Word}
    (h : (s', t, ws) ∈ evalOp g env σs s (.publish a)) : s' = fenceS s .st ∧ ∃ t0, evalAt env a = some (t0, ws) := by
  simp only [evalOp, ol] at h
  cases ho : evalAt env a with
  | none => simp [ho] at h
  | some r =>
    obtain ⟨t0, ws0⟩ := r
    simp only [ho, bind, Option.bind] at h
    split at h <;> simp_all

/-- **One thread step of main keeps `TInv`**, memory only grows. -/
theorem tinv_tstep {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh}
    (hg : g.p = wakeSrc) (hi : TInv mem.size th) (h : (mem', pairs', th') ∈ tstep g mem pairs th) :
    mem.size ≤ mem'.size ∧ TInv mem'.size th' := by
  obtain ⟨hm, hst, hv, he, hz, hn⟩ := hi
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
      refine ⟨Nat.le_refl _, Or.inr (Or.inl hb), hst, hv, EnvB.cons (fun _ h => by simp at h) (he.lookup hme),
        fun h => ?_, fun h => ?_⟩
      · simp [hb, mBody, mZ] at h
      · simp [hb, mBody, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "z" (.zero .int) mZ) rfl] at h
    have hcl : close th.σs Ty.int = .int := rfl
    simp [evalOp, ol, stOf, hcl, zeroWords] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨Nat.le_refl _, Or.inr (Or.inr (Or.inl rfl)), hst, hv, EnvB.cons he (cst_b _ _), fun _ => ?_, fun h => ?_⟩
    · simp [lookupE, withS]
    · simp [withS, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · obtain ⟨_, _, _, h, tys, hr⟩ := tstep_new_mem (ht.trans rfl : th.term = .let_ "o" (.new (.var "z") (some .int)) mO) h
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
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨hlt, hvb, rfl⟩ := alloc_vb (s := stOf mem pairs th) hv ha
      refine ⟨Nat.le_of_lt hlt, Or.inr (Or.inr (Or.inr (Or.inl rfl))), hst, hvb,
        EnvB.cons (he.mono (by simp only [stOf] at hlt; omega)) (cst_b _ _), fun h => ?_,
        fun _ => by simp only [stOf] at hlt; omega⟩
      simp [withS, mO, mZ] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "c" (.publish (.var "o")) mC) rfl] at h
    obtain ⟨⟨s', t, ws⟩, hr, rfl, rfl, rfl⟩ := List.mem_map.mp h
    obtain ⟨rfl, t0, ho⟩ := publish_res hr
    have hw := he.lookup ho
    have hn' := hn (Or.inl ht)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
    refine ⟨Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hst,
      ⟨h1, h2, h3, h4, ?_, h6⟩, EnvB.cons he hw, fun h => ?_, fun _ => hn'⟩
    · simp only [withS, fenceS, stOf, Promises.stepFence, mth, WeakMem.Ts] at h5 h2 ⊢; omega
    · simp [withS, mC, mZ] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm) rfl] at h
    cases hc : evalAt th.env (.var "c") with
    | none => simp [evalOp, ol, hc] at h
    | some r =>
    cases hm : evalAt th.env (.var "me") with
    | none => simp [evalOp, ol, hc, hm] at h
    | some r' =>
      obtain ⟨t, ws⟩ := r
      obtain ⟨t', ws'⟩ := r'
      have hw : ∀ w ∈ ws ++ ws', w.view ≤ mem.size - 1 ∧ w.rts ≤ mem.size - 1 := by
        intro w hw; rcases List.mem_append.mp hw with hw | hw
        · exact he.lookup hc w hw
        · exact he.lookup hm w hw
      simp [evalOp, ol, hc, hm, stOf, withS] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hst, hv, EnvB.cons he hw,
        fun h => ?_, fun _ => hn (Or.inr (Or.inl ht))⟩
      simp [spawnTerm, WakePreA.spawnTerm, mZ] at h
  · rw [TermLocal.tstep_let_gen
      (ht.trans rfl : th.term = .let_ "t" (.spawn "worker" (.var "p") (.prod (.ptr .pub .int) .tid) []) mTail) rfl] at h
    simp [evalOp] at h

/-! ## Along source runs -/

theorem idx0 {s : Cfg} {i : Nat} {th : TTh} (h1 : s.ths.size = 1) (h : s.ths[i]? = some th) : i = 0 := by
  have := (Array.getElem?_eq_some_iff.mp h).1; omega

theorem not_ext {th : TTh} (hm : MainPre th.term) {x : String} {n : ExtName} {a : At} {e : Expr}
    (h : th.term = .let_ x (.ext n a) e) : False := by
  rcases hm with hm | hm | hm | hm | hm | hm <;> rw [hm] at h <;>
    simp [mStart, mBody, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h

/-- **One source step keeps `VPre`.** -/
theorem vpre_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (wakeS arch).step i s es s')
    (hv : VPre s) : VPre s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have hsz := stepBy_size hs
    obtain ⟨th0, h0, hi⟩ := hv (hsz ▸ h1')
    have h1 : s.ths.size = 1 := hsz ▸ h1'
    rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
    · unfold TermRun.threadSteps at hm
      split at hm
      · simp at hm
      · rename_i th hth
        obtain rfl := idx0 h1 hth
        rw [h0] at hth; cases hth
        obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
        obtain ⟨-, hi2⟩ := tinv_tstep rfl hi hr
        exact ⟨th', getElem?_set!_self h0 _, hi2⟩
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise
      rw [h0]
      exact ⟨_, getElem?_set!_self h0 _, hi.mono (by simp)⟩
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

theorem vpre_init {arch : Arch} {s : Cfg} (h : (wakeS arch).init s) : VPre s := by
  have h' : s = WakeT1.tidStartT 2 := by
    change WakeT1.progInitT wakeSrc 2 s at h
    rw [wake_start] at h
    exact h
  subst h'
  intro _
  refine ⟨_, rfl, Or.inl rfl, rfl, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · exact ⟨Nat.le_of_eq rfl, Nat.le_of_eq rfl, Nat.le_of_eq rfl, Nat.le_of_eq rfl, Nat.le_of_eq rfl,
      fun _ => Nat.le_of_eq rfl⟩
  · intro p hp w hw
    simp [WakeT1.tidStartT] at hp
    subst hp
    simp at hw
    subst hw
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp [WakeT1.tidStartT, mZ] at h
  · simp [WakeT1.tidStartT, mO, mC, spawnTerm, WakePreA.spawnTerm] at h

/-- **`VPre` along source runs.** -/
theorem vpre_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (wakeS arch).Run s tr s') (hv : VPre s) :
    VPre s' := by
  induction h with
  | refl => exact hv
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vpre_step hs hv)

/-- **Strict bounds at main's spawn**: with one thread, at `spawnTerm`, its
views (`SpawnVLt`, at every address) and its environment's words (`EnvLt`)
are below the memory size. -/
theorem vpre_spawn {s : Cfg} {th0 : TTh} (hv : VPre s) (h1 : s.ths.size = 1) (h0 : s.ths[0]? = some th0)
    (ht : th0.term = spawnTerm) : (∀ a, SpawnVLt th0 a s.mem.size) ∧ EnvLt th0 s.mem.size := by
  obtain ⟨th, h0', hi⟩ := hv h1
  rw [h0] at h0'; cases h0'
  obtain ⟨-, -, ⟨h1, h2, h3, h4, h5, h6⟩, he, -, hn⟩ := hi
  have hn := hn (Or.inr (Or.inr ht))
  refine ⟨fun a => ?_, ?_⟩
  · have h6 := h6 a
    simp only [SpawnVLt, WeakMem.Ts] at *
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  intro p hp w hw
  have := he p hp w hw
  simp only [WeakMem.Ts] at *
  omega

/-! ## The spawn step -/

/-- After the spawn, main is at `mTail`: it has not returned. -/
theorem mainExit_spawnCfg {s : Cfg} {th0 : TTh} (h0 : s.ths[0]? = some th0) (ws : List Word) :
    mainExit (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) = [] := by
  have hs : (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws).ths[0]? =
      some (TermSpawnStep.spawnPar s 0 th0 "t" mTail) := by
    have hlt := (Array.getElem?_eq_some_iff.mp h0).1
    simp only [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT]
    rw [Array.getElem?_push]
    split
    · rename_i h; simp at h; omega
    · exact getElem?_set!_self h0 _
  unfold mainExit
  rw [hs]
  simp [TermSpawnStep.spawnPar, mTail]

/-- **main's spawn is a source run with the empty trace.** -/
theorem run_spawnCfg {arch : Arch} {s : Cfg} {th0 : TTh} {rt : Ty} {ws : List Word}
    (h0 : s.ths[0]? = some th0) (ht : th0.term = spawnTerm) (hp : th0.promises = []) (hcap : s.ths.size < 2)
    (hev : evalAt th0.env (.var "p") = some (rt, ws)) (hex : mainExit s = []) :
    (wakeS arch).Run s []
      (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) := by
  have hstep : (wakeS arch).step 0 s []
      (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) := by
    refine ⟨hex, Or.inr (Or.inl ⟨"t", "worker", .var "p", _, [], mTail, th0, rt, ws, h0, ht, hp, hcap, hev, rfl⟩), ?_⟩
    have htr : (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws).trace =
        s.trace := rfl
    show [] = (srcObs traceOf _).drop (srcObs traceOf s).length
    simp only [srcObs, traceOf, htr, hex, mainExit_spawnCfg h0, List.drop_length]
  exact LRun.step (step := fun c es c' => ∃ i, (wakeS arch).step i c es c') ⟨0, hstep⟩ (LRun.refl _)

/-! ## main's source fields past the spawn -/

/-- **main's fields at the spawn's parent**: at `mTail`, `c` bound to the
pointer word `cst (.loc ⟨l, 0⟩ 0)`, which represents `A` (as value and as
location) when `l` is placed at `A`, and is in bounds when `l` has a word. -/
theorem src_fields {s : Cfg} {i : Nat} {th0 : TTh} {l : WeakMem.AllocLabel}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {A : Nat}
    (hc : evalAt th0.env (.var "c") = some (.ptr .pub .int, [cst (.loc ⟨l, 0⟩ 0)])) (hA : lbl l = some A)
    (hlsz : 0 < lsize l) :
    (Ctl.of (TermSpawnStep.spawnPar s i th0 "t" mTail)).term = mTail ∧
      lookupE (Ctl.of (TermSpawnStep.spawnPar s i th0 "t" mTail)).env "c" =
        some (.ptr .pub .int, [cst (.loc ⟨l, 0⟩ 0)]) ∧
      (cst (.loc ⟨l, 0⟩ 0)).val = .loc ⟨l, 0⟩ 0 ∧
      ValRep lbl (cst (.loc ⟨l, 0⟩ 0)).val A ∧
      LocRep lbl (cst (.loc ⟨l, 0⟩ 0)).val A 0 ∧
      ∃ sa, (cst (.loc ⟨l, 0⟩ 0)).val = .loc sa 0 ∧ sa.offset < lsize sa.label := by
  refine ⟨rfl, ?_, rfl, ⟨by decide, A, by simp [wordAddr, hA], rfl⟩, ⟨rfl, hA, rfl⟩, ⟨_, rfl, hlsz⟩⟩
  simp only [evalAt] at hc
  simp [Ctl.of, TermSpawnStep.spawnPar, withS, lookupE] at hc ⊢
  exact hc

/-- info: 'Spike.Lib.SpawnViewLtSteps.vpre_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vpre_init

/-- info: 'Spike.Lib.SpawnViewLtSteps.vpre_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vpre_run

/-- info: 'Spike.Lib.SpawnViewLtSteps.vpre_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vpre_spawn

/-- info: 'Spike.Lib.SpawnViewLtSteps.run_spawnCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_spawnCfg

/-- info: 'Spike.Lib.SpawnViewLtSteps.src_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms src_fields

end Spike.Lib.SpawnViewLtSteps
