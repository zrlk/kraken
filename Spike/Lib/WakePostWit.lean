/-
**wake.w on AArch64: the witness after the spawn** (`WakeAssembly`'s
`post_wit`): every pair related by `WakeRel.Post` at a configuration with the
run invariant (`WakeRunInv.RunInv`) has a witness for `Components`.

The witness (`postW`) maps source thread `i` to target thread `i` (`i < 2`),
takes the placement, sizes and timestamp map of `Inv2Core.mem` (the spawn's
record `SR w`), and frame 0's environment of each thread from its placed
environment (`A64Consumer.Placed`); no marked place, no epochs, target
epochs from the last timestamp. The memory clauses are `Inv2Core.mem`'s
(`Components.ofMemRelP`, no unmirrored promise), the stack clauses
`WakeStack.stackOk_run`'s.

- `postW`: the witness.
- `post_wit_gen`: for any relation data whose per-thread relations give a
  one-frame source thread and a placed environment (`hpl0`, `hpl1`).
- `post_wit_of`: for relation data with wake's per-thread relations
  (`Q.PT0 = WakeM0.PT0 M`, `Q.PT1 = WakeW1.PT1 D`: `WakeQ.hPT0`,
  `WakeQ.pt1`, both `rfl` at `WakeQ.wakeQ`), from main's and the worker's
  invariants placing the environment (`hplM`, `hplW`); main's source after
  its return (`wlRet`) reads no variable (`placed_wlRet`).
-/
import Spike.Lib.WakeStackPost
import Spike.Lib.WakeM0
import Spike.Lib.WakeW1

namespace Spike.Lib.WakePostWit

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.A64Consumer (Placed)

/-- The machine after the spawn. -/
abbrev M2 : ExtMachine := machine (kernel 2)

/-- **The witness after the spawn**: threads `0` and `1` to themselves, the
placement `lbl`, sizes `lsize` and timestamp map `ts`, frame 0's
environment of thread `i` from `e i`, no marked place, no epochs, target
epochs from `last`. -/
def postW (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat)
    (e : Nat → String → Nat → Option (WordPlace M2.I.RegId)) (last : Nat) : Witness M2 where
  thr i := if i < 2 then some i else none
  lbl := lbl
  lsize := lsize
  ts := ts
  env i d x k := if d = 0 then e i x k else none
  marked _ _ := False
  since _ := 0
  tsFrom _ := last

/-- The body of `Placed` at a given environment map. -/
def PlacedBy (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat) (s : State) (c : Ctl)
    (envm : String → Nat → Option (WordPlace M2.I.RegId)) : Prop :=
  (∀ x ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k wd wp, ws[k]? = some wd → envm x k = some wp →
      WordPlaceRep M2 lbl s wp wd.val) ∧
    (∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k < ws.length,
      ∃ pl, envm x k = some pl) ∧
    (∀ x k n, envm x k = some (.imm n) → Λ.imms c.term x k = some n)

theorem placedBy_of {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {s : State} {c : Ctl}
    (h : Placed Λ lbl s c) : ∃ envm, PlacedBy Λ lbl s c envm := h

/-- **The witness for any relation data**: each per-thread relation gives a
one-frame source thread with a placed environment at the spawn's
placement. -/
theorem post_wit_gen {Q : WakeRel} {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {E : Entry}
    (hpl0 : ∀ w tm sm tt st, Q.PT0 w tm sm tt st → st.stack = [] ∧ Placed Λ (Q.SR w).lbl tt.st (Ctl.of st))
    (hpl1 : ∀ w tm sm tt st, Q.PT1 w tm sm tt st → st.stack = [] ∧ Placed Λ (Q.SR w).lbl tt.st (Ctl.of st))
    {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) (hr : WakeRunInv.RunInv Λ E t) :
    ∃ w, Components M2 Λ w t s := by
  have hP := h
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hsth, hc, hp0, hp1, -⟩, -⟩ := h
  simp only [WakeRel.PTw, ite_true, show (1 : Nat) ≠ 0 from by decide, ite_false] at hp0 hp1
  obtain ⟨hst0, hq0⟩ := hpl0 w _ _ _ _ hp0.2
  obtain ⟨hst1, hq1⟩ := hpl1 w _ _ _ _ hp1
  obtain ⟨e0, he0⟩ := placedBy_of hq0
  obtain ⟨e1, he1⟩ := placedBy_of hq1
  let e : Nat → String → Nat → Option (WordPlace M2.I.RegId) := fun i => if i = 0 then e0 else e1
  let W := postW (Q.SR w).lbl (Q.SR w).lsize ts e t.1.mem.last
  -- each source thread: its target thread, one frame, placed by `e i`
  have hrow : ∀ i th, s.ths[i]? = some th → i < 2 ∧ ∃ tt, t.1.threads[i]? = some tt ∧ th.stack = [] ∧
      PlacedBy Λ (Q.SR w).lbl tt.st (Ctl.of th) (e i) := by
    intro i th hi
    rw [hsth] at hi
    rcases i with _ | _ | i
    · cases (show s0 = th by simpa using hi)
      exact ⟨by decide, t0, by rw [hth]; rfl, hst0, he0⟩
    · cases (show s1 = th by simpa using hi)
      exact ⟨by decide, t1, by rw [hth]; rfl, hst1, he1⟩
    · simp at hi
  have hsize : t.1.threads.size = 2 := by rw [hth]; rfl
  have hthr : ∀ {i j}, W.thr i = some j → i < 2 ∧ j = i := by
    intro i j hj
    simp only [W, postW] at hj
    split at hj
    · exact ⟨by assumption, (Option.some.inj hj).symm⟩
    · cases hj
  refine ⟨W, Components.ofMemRelP (tq := []) hc.mem ?_ (fun _ => rfl) (fun _ q hq => by cases hq)
    (fun q hq => by cases hq)⟩
  have hso := WakeStack.stackOk_run (w := W) hwf hP hr (fun _ _ h => h)
  refine
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := hso.stack_pool, stack_disj := hso.stack_disj, stack_owned := hso.stack_owned,
      stack_private := hso.stack_private, stack_marked := hso.stack_marked,
      stack_unmarked := hso.stack_unmarked, env_imm := ?_ }
  · intro i hi
    rw [hsth] at hi
    have hi' : i < 2 := by simpa using hi
    exact ⟨i, by simp [W, postW, hi'], Nat.lt_of_lt_of_eq hi' hsize.symm⟩
  · intro i i' j h h'
    obtain ⟨-, h1⟩ := hthr h
    obtain ⟨-, h2⟩ := hthr h'
    omega
  · intro j tt _ hj
    have hj2 : j < 2 := by
      rw [← hsize]; exact (Array.getElem?_eq_some_iff.mp hj).1
    exact ⟨j, by rw [hsth]; simpa using hj2, by simp [W, postW, hj2]⟩
  · intro i th j tt hi hj htt d en hd x ty ws hx k wd wp hwd hwp _
    obtain ⟨-, hji⟩ := hthr hj
    subst j
    obtain ⟨-, tt', htt', hst, hpb, -, -⟩ := hrow i th hi
    have htt2 : (some tt : Option (Thread isaLSE2)) = some tt' := htt.symm.trans htt'
    cases htt2
    simp only [frameEnvs, hst, List.map_nil] at hd
    rcases d with _ | d
    · cases (show th.env = en by simpa using hd)
      simp only [W, postW, ite_true] at hwp
      exact hpb x ty ws hx k wd wp hwd hwp
    · simp at hd
  · intro i th hi d en xs hd hxs _ x hx ty ws hl k hk
    obtain ⟨-, tt, -, hst, -, htot, -⟩ := hrow i th hi
    simp only [frameEnvs, frameFv, hst, List.map_nil] at hd hxs
    rcases d with _ | d
    · cases (show th.env = en by simpa using hd)
      cases (show exprFv th.term = xs by simpa using hxs)
      obtain ⟨pl, hpl⟩ := htot x hx ty ws hl k hk
      exact ⟨pl, by simp only [W, postW, ite_true]; exact hpl⟩
    · simp at hd
  · intro i th d en x k n hi hd hx
    obtain ⟨-, tt, -, hst, -, -, himm⟩ := hrow i th hi
    simp only [frameTerms, hst, List.map_nil] at hd
    rcases d with _ | d
    · cases (show th.term = en by simpa using hd)
      simp only [W, postW, ite_true] at hx
      exact himm x k n hx
    · simp [W, postW] at hx

/-- **main's source after its return is placed**: `wlRet` reads no
variable, so the empty environment map places it. -/
theorem placed_wlRet {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {s : State} {c : Ctl}
    (h : c.term = WakeMLive.wlRet) : Placed Λ lbl s c := by
  refine ⟨fun _ _ => none, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h; cases h
  · intro x hx
    rw [h] at hx
    simp [WakeMLive.wlRet, exprFv, atVars] at hx
  · intro _ _ _ h; cases h

/-- **`post_wit` at wake's per-thread relations** (`WakeQ.wakeQ`: `hPT0`
and `hPT1` are `WakeQ.hPT0`, `WakeQ.pt1`): main's invariant (`hplM`, owner:
main's side) and the worker's (`hplW`, owner: the worker's side) place
their thread's environment at the spawn's placement. -/
theorem post_wit_of {Q : WakeRel} {M : WakeM0.MSide Q.ι} {D : WakeW1.WSide Q.ι}
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hPT1 : Q.PT1 = WakeW1.PT1 D)
    {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {E : Entry}
    (hplM : ∀ w s c, M.Mi w s c → Placed Λ (Q.SR w).lbl s c)
    (hplW : ∀ w s c, D.Wi w s c → Placed Λ (Q.SR w).lbl s c) :
    ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components M2 Λ w t s :=
  fun _ _ h hr => post_wit_gen hwf
    (fun w _ _ _ _ hp => by
      rw [hPT0] at hp
      obtain ⟨h1, h2, -⟩ := hp
      -- `PT0`'s first conjunct: `Mi ∨ term = wlRet` (or `Mi` alone before that widening)
      exact ⟨h2, h1.elim (hplM w _ _) fun h => placed_wlRet h⟩)
    (fun w _ _ _ _ hp => by
      rw [hPT1] at hp
      obtain ⟨h1, h2, -⟩ := hp
      exact ⟨h2, hplW w _ _ h1⟩) h hr

/-- info: 'Spike.Lib.WakePostWit.post_wit_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakePostWit.post_wit_gen

/-- info: 'Spike.Lib.WakePostWit.post_wit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakePostWit.post_wit_of

end Spike.Lib.WakePostWit
