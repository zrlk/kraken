/-
**The witness after the spawn, every frame placed** (generic
part; the multi-frame twin of `X64WakePostWit.post_wit_gen`, which places one
frame of each thread): every pair related by `WakeRel.Post` at a
configuration with the run invariant has a witness for `Components`, when
each per-thread relation places its source thread's frames at the spawn's
placement (`X64ConsumerS.PlacedSE`: every frame placed, or the current frame
in the output extern's model or reading no variable with the suspended
frames placed).

The witness (`postWS`) is `X64WakePostWit.postW` with frame `d`'s environment
of thread `i` from `e i d` (`postW` has frame 0's only). The memory clauses
are `Inv2Core.mem`'s (`Components.ofMemRelP`), the stack clauses
`X64WakeStack.stackOk_run`'s, as at `post_wit_gen`.

- `PlacedC`: `Components`' three environment clauses at one thread pair.
- `placedC_of`: `PlacedC` from `PlacedSE` (`PlacedS` directly; at the extern
  model, frame 0 empty and the suspended frames by `FramesPlaced`).
- `postWS`: the witness.
- `post_wit_genSE`: the statement.

x86-64 twin of `Spike/Lib/HelloPostWitG.lean` (same names, namespaces with the `X64` prefix).
-/
import Spike.Lib.X64WakePostWit
import Spike.Lib.X64PlacedSE

namespace Spike.Lib.X64HelloPostWitG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64ConsumerS (PlacedSE PlacedS FramesPlaced envsOf termsOf fvOf)
open Spike.Lib.X64WakePostWit (M2)

/-- An environment map per frame. -/
abbrev EnvM : Type := Nat → String → Nat → Option (WordPlace M2.I.RegId)

/-- **`Components`' environment clauses at one thread pair** (`env_rep`,
`env_total`, `env_imm` at source thread `th`, target thread `tt` and frame
`d`'s environment map `envm d`). -/
def PlacedC (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat) (tt : Thread isa) (th : TermRun.TTh)
    (envm : EnvM) : Prop :=
  (∀ d e, (frameEnvs th)[d]? = some e → ∀ x ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → ¬ ExternFrame th d →
      WordPlaceRep M2 lbl tt.st wp wd.val) ∧
  (∀ d e xs, (frameEnvs th)[d]? = some e → (frameFv th)[d]? = some xs → ¬ ExternFrame th d →
    ∀ x ∈ xs, ∀ ty ws, TermRun.lookupE e x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
  (∀ d e x k n, (frameTerms th)[d]? = some e → envm d x k = some (.imm n) → Λ.imms e x k = some n)

/-- **`PlacedC` from `PlacedSE`**: at `PlacedS` its map; at the output
extern's model (or a term reading no variable) frame 0 empty and the
suspended frames by `FramesPlaced`, as in `X64ConsumerA.components_oneSEH`. -/
theorem placedC_of {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {tt : Thread isa}
    {th : TermRun.TTh} (h : PlacedSE Λ lbl tt.st (Ctl.of th) th.stack) : ∃ envm, PlacedC Λ lbl tt th envm := by
  rcases h with ⟨envm, hrep, htot, himm⟩ | ⟨hext, envf, hrep, htot, himm⟩
  · exact ⟨envm, fun d e hd x ty ws hx k wd wp hwd hwp _ => hrep d e hd x ty ws hx k wd wp hwd hwp,
      fun d e xs hd hxs _ x hx ty ws hl k hk => htot d e xs hd hxs x hx ty ws hl k hk,
      fun d e x k n hd hx => himm d e x k n hd hx⟩
  · refine ⟨fun d => match d with | 0 => fun _ _ => none | d + 1 => envf d, ?_, ?_, ?_⟩
    · intro d e hd x ty ws hx k wd wp hwd hwp _
      rcases d with _ | d
      · cases hwp
      · simp only [frameEnvs, List.getElem?_cons_succ, List.getElem?_map] at hd
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
        exact hrep d f hf x ty ws hx k wd wp hwd hwp
    · intro d e xs hd hxs hxf x hx ty ws hl k hk
      rcases d with _ | d
      · simp only [frameFv, List.getElem?_cons_zero, Option.some.injEq] at hxs
        subst hxs
        rcases hext with h | h
        · exact absurd ⟨rfl, h⟩ hxf
        · rw [show (Ctl.of th).term = th.term from rfl] at h
          rw [h] at hx; cases hx
      · simp only [frameEnvs, List.getElem?_cons_succ, List.getElem?_map] at hd
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
        simp only [frameFv, List.getElem?_cons_succ, List.getElem?_map, hf, Option.map_some,
          Option.some.injEq] at hxs
        subst hxs
        exact htot d f hf x hx ty ws hl k hk
    · intro d e x k n hd hx
      rcases d with _ | d
      · cases hx
      · simp only [frameTerms, List.getElem?_cons_succ, List.getElem?_map] at hd
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
        exact himm d f x k n hf hx

/-- **The witness after the spawn, every frame**: threads `0` and `1` to
themselves, the placement `lbl`, sizes `lsize` and timestamp map `ts`,
frame `d`'s environment of thread `i` from `e i d`, no marked place, no
epochs, target epochs from `last`. -/
def postWS (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat)
    (e : Nat → EnvM) (last : Nat) : Witness M2 where
  thr i := if i < 2 then some i else none
  lbl := lbl
  lsize := lsize
  ts := ts
  env i := e i
  marked _ _ := False
  since _ := 0
  tsFrom _ := last

/-- **The witness for any relation data whose per-thread relations place
every frame** (`hpl0`, `hpl1`: `PlacedSE` at the spawn's placement). -/
theorem post_wit_genSE {Q : WakeRel} {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {E : Entry}
    (hpl0 : ∀ w tm sm tt st, Q.PT0 w tm sm tt st → PlacedSE Λ (Q.SR w).lbl tt.st (Ctl.of st) st.stack)
    (hpl1 : ∀ w tm sm tt st, Q.PT1 w tm sm tt st → PlacedSE Λ (Q.SR w).lbl tt.st (Ctl.of st) st.stack)
    {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) (hr : X64WakeRunInv.RunInv Λ E t) :
    ∃ w, Components M2 Λ w t s := by
  have hP := h
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hsth, hc, hp0, hp1, -⟩, -⟩ := h
  simp only [WakeRel.PTw, ite_true, show (1 : Nat) ≠ 0 from by decide, ite_false] at hp0 hp1
  obtain ⟨e0, he0⟩ := placedC_of (hpl0 w _ _ _ _ hp0.2)
  obtain ⟨e1, he1⟩ := placedC_of (hpl1 w _ _ _ _ hp1)
  let e : Nat → EnvM := fun i => if i = 0 then e0 else e1
  let W := postWS (Q.SR w).lbl (Q.SR w).lsize ts e t.1.mem.last
  -- each source thread: its target thread, placed by `e i`
  have hrow : ∀ i th, s.ths[i]? = some th → i < 2 ∧ ∃ tt, t.1.threads[i]? = some tt ∧
      PlacedC Λ (Q.SR w).lbl tt th (e i) := by
    intro i th hi
    rw [hsth] at hi
    rcases i with _ | _ | i
    · cases (show s0 = th by simpa using hi)
      exact ⟨by decide, t0, by rw [hth]; rfl, he0⟩
    · cases (show s1 = th by simpa using hi)
      exact ⟨by decide, t1, by rw [hth]; rfl, he1⟩
    · simp at hi
  have hsize : t.1.threads.size = 2 := by rw [hth]; rfl
  have hthr : ∀ {i j}, W.thr i = some j → i < 2 ∧ j = i := by
    intro i j hj
    simp only [W, postWS] at hj
    split at hj
    · exact ⟨by assumption, (Option.some.inj hj).symm⟩
    · cases hj
  refine ⟨W, Components.ofMemRelP (tq := []) hc.mem ?_ (fun _ => rfl) (fun _ q hq => by cases hq)
    (fun q hq => by cases hq)⟩
  have hso := X64WakeStack.stackOk_run (w := W) hwf hP hr (fun _ _ h => h)
  refine
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := hso.stack_pool, stack_disj := hso.stack_disj, stack_owned := hso.stack_owned,
      stack_private := hso.stack_private, stack_marked := hso.stack_marked,
      stack_unmarked := hso.stack_unmarked, env_imm := ?_ }
  · intro i hi
    rw [hsth] at hi
    have hi' : i < 2 := by simpa using hi
    exact ⟨i, by simp [W, postWS, hi'], Nat.lt_of_lt_of_eq hi' hsize.symm⟩
  · intro i i' j h h'
    obtain ⟨-, h1⟩ := hthr h
    obtain ⟨-, h2⟩ := hthr h'
    omega
  · intro j tt _ hj
    have hj2 : j < 2 := by
      rw [← hsize]; exact (Array.getElem?_eq_some_iff.mp hj).1
    exact ⟨j, by rw [hsth]; simpa using hj2, by simp [W, postWS, hj2]⟩
  · intro i th j tt hi hj htt d en hd x ty ws hx k wd wp hwd hwp hxf
    obtain ⟨-, hji⟩ := hthr hj
    subst j
    obtain ⟨-, tt', htt', hpc⟩ := hrow i th hi
    have htt2 : (some tt : Option (Thread isa)) = some tt' := htt.symm.trans htt'
    cases htt2
    exact hpc.1 d en hd x ty ws hx k wd wp hwd hwp hxf
  · intro i th hi d en xs hd hxs hxf x hx ty ws hl k hk
    obtain ⟨-, tt, -, hpc⟩ := hrow i th hi
    exact hpc.2.1 d en xs hd hxs hxf x hx ty ws hl k hk
  · intro i th d en x k n hi hd hx
    obtain ⟨-, tt, -, hpc⟩ := hrow i th hi
    exact hpc.2.2 d en x k n hd hx

/-- info: 'Spike.Lib.X64HelloPostWitG.placedC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placedC_of

/-- info: 'Spike.Lib.X64HelloPostWitG.post_wit_genSE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_wit_genSE

end Spike.Lib.X64HelloPostWitG
