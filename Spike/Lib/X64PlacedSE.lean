/-
**The frames placed, or the current frame in the output extern's model**
(x86-64): `PlacedSE`, the placement field of the arena consumer's
obligations (`NodesA.place`), of `SFactsA` and of `W2`: every frame placed
(`PlacedS`), or the current control at a model term of the output extern
(`Scc.Sem.ExternFrame`, exempt from `env_rep` and `env_total`) or at a term
reading no variable, with the suspended frames placed (`FramesPlaced`).
`Components` holds at either (`components_oneSX`).

- `PlacedSE`, `PlacedSE.of_placedS`, `PlacedSE.of_ext`, `PlacedSE.frames`: the placement.
- `PostSA`, `post_progressSA`: `PostS` at `PlacedSE` (the arena consumers'
  state after the exit).
- `components_oneSE`: `components_oneS` with the current frame unplaced, at
  a model term or a term reading no variable.
- `components_oneSX`: `Components` for a one-thread pair at `PlacedSE`.

The twin of `Spike/Lib/A64PlacedSE.lean`.
-/
import Spike.Lib.X64PlacedS
import Scc.Sem.Correct

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer

/-- **The frames placed, or the current frame in the output extern's
model**: `PlacedS`, or the control's term a model term of the output extern
or reading no variable and the suspended frames placed. -/
def PlacedSE (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  PlacedS Λ lbl s c fs ∨ ((c.term ∈ externModelTerms ∨ exprFv c.term = []) ∧ FramesPlaced Λ lbl s fs)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}

theorem PlacedSE.of_placedS (h : PlacedS Λ lbl s c fs) : PlacedSE Λ lbl s c fs := .inl h

theorem PlacedSE.of_ext (h : c.term ∈ externModelTerms ∨ exprFv c.term = []) (hf : FramesPlaced Λ lbl s fs) :
    PlacedSE Λ lbl s c fs :=
  .inr ⟨h, hf⟩

/-- **The suspended frames are placed** at either disjunct. -/
theorem PlacedSE.frames (h : PlacedSE Λ lbl s c fs) : FramesPlaced Λ lbl s fs :=
  h.elim PlacedS.frames fun h => h.2

/-- **After the exit** at any depth, the frames at `PlacedSE` (`PostS` with
the current frame possibly in the output extern's model: an abort of the
output `write` ends the process inside `print`). -/
def PostSA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (rS : Range) (Tk : State → Prop)
    (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (o : Outcome),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = { KS E Λ j hl pm with exited := some o }) ∧ (∀ a, Kernel.byte pm a = 0) ∧
    HeldOk Λ rS Tk th.st hl ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    PlacedSE Λ lbl th.st (Ctl.of th0) th0.stack ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧ OwnMsgs t.1.mem ∧
    MemIn Λ t.1.mem ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **There is progress after the exit** (`post_progressS` at `PostSA`). -/
theorem post_progressSA {P : SrcSem.SrcParams} {p : Prog} {μ : Marks} {rS : Range} {Tk : State → Prop}
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PostSA Λ P p rS Tk t s) : T.M.Progress μ t := by
  obtain ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩ := h
  exact Kernel.exited_progress abi (o := o) (by rw [hk])

end Spike.Lib.X64ConsumerS

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {Λ : Scc.Sem.Layout}

/-- **`Components` for a one-thread pair with the current frame in the
output extern's model** (`components_oneS` with the current frame unplaced):
its term is a model term (`ExternFrame`, exempt from `env_rep` and
`env_total`) or reads no variable; the suspended frames by `FramesPlaced`. -/
theorem components_oneSE (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat} {rS : Range} {Tk : State → Prop}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl) (hh : HeldOk Λ rS Tk th.st hl)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0])
    (hext : th0.term ∈ externModelTerms ∨ exprFv th0.term = []) (hpl : FramesPlaced Λ lbl th.st th0.stack)
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  obtain ⟨envf, hrep, htot, himm⟩ := hpl
  let envm : Nat → String → Nat → Option (WordPlace T.M.I.RegId) := fun d => match d with
    | 0 => fun _ _ => none
    | d + 1 => envf d
  have hsr : ∀ j rg, T.M.stackRange t j = some rg → j = 0 ∧ rg = rS ∧ Owned Λ rS th.st := by
    intro j rg h
    change Kernel.stackRangeOf abi t j = some rg at h
    unfold Kernel.stackRangeOf at h
    split at h
    · cases h
    · rename_i tt htt
      obtain ⟨rfl, rfl⟩ := get_one hth htt
      rw [hheld] at h
      rcases hh with ⟨rfl, -⟩ | ⟨rfl, -, ho⟩
      · simp at h
      · refine ⟨rfl, ?_, ho⟩
        simp only [List.find?_cons, List.find?_nil] at h
        split at h
        · exact (Option.some.inj h).symm
        · cases h
  have hs1 : ∀ {i} {th'}, s.ths[i]? = some th' → i = 0 ∧ th' = th0 := by
    intro i th' h
    rw [hs0] at h
    rcases i with _ | i
    · exact ⟨rfl, (Option.some.inj h).symm⟩
    · simp at h
  refine ⟨witS lbl lsize ts envm t.1.mem.last, Components.ofMemRelP (tp := []) (sp := []) hinv.mem
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := (fun j rg h => by obtain ⟨-, rfl, ho⟩ := hsr j rg h; exact ho.1),
      stack_disj := (fun j j' rg rg' hne h h' => absurd ((hsr j rg h).1.trans (hsr j' rg' h').1.symm) hne),
      stack_owned := (fun j rg h j' tt' htt a h8 h1 h2 => by
        obtain ⟨rfl, rfl, ho⟩ := hsr j rg h
        obtain ⟨rfl, rfl⟩ := get_one hth htt
        exact ⟨fun _ => rfl, fun _ => ho.2 a h8 h1 h2⟩),
      stack_private := (fun j rg h m hm hc => by
        obtain ⟨-, rfl, ho⟩ := hsr j rg h
        exact shared_not_pool hwf (memIn_msgs hmi m hm).addr (sub_contains ho.1 hc)),
      stack_marked := fun _ _ h => h.elim,
      stack_unmarked := fun _ _ _ _ _ _ _ _ _ _ h => h, env_imm := ?_ }
    (fun _ => rfl) (fun _ q hq => (hinv.mem.tq_le q hq).2) ?_, rfl⟩
  · intro i hi
    rw [hs0] at hi
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨0, rfl, by rw [hth]; exact Nat.zero_lt_one⟩
  · intro i i' j h h'
    simp only [witS] at h h'
    by_cases hi : i = 0 <;> by_cases hi' : i' = 0
    · rw [hi, hi']
    · simp [hi'] at h'
    · simp [hi] at h
    · simp [hi] at h
  · intro j tt _ hj
    obtain ⟨rfl, -⟩ := get_one hth hj
    exact ⟨0, by rw [hs0]; exact Nat.zero_lt_one, rfl⟩
  · intro i th' j tt hi hj htt d e hd x ty ws hx k wd wp hwd hwp _hxf
    obtain ⟨rfl, rfl⟩ := hs1 hi
    simp only [witS, ite_true, Option.some.injEq] at hj
    subst hj
    obtain ⟨-, rfl⟩ := get_one hth htt
    simp only [witS, ite_true] at hwp
    rcases d with _ | d
    · cases hwp
    · simp only [frameEnvs, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact hrep d f hf x ty ws hx k wd wp hwd hwp
  · intro i th' hi d e xs hd hxs hxf x hx ty ws hl k hk
    obtain ⟨rfl, rfl⟩ := hs1 hi
    rcases d with _ | d
    · simp only [frameFv, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hxs
      rcases hext with h | h
      · exact absurd ⟨rfl, h⟩ hxf
      · rw [h] at hx; cases hx
    · simp only [frameEnvs, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      simp only [frameFv, List.getElem?_cons_succ, List.getElem?_map, hf, Option.map_some,
        Option.some.injEq] at hxs
      subst hxs
      obtain ⟨pl, hpl⟩ := htot d f hf x hx ty ws hl k hk
      exact ⟨pl, by simp only [witS, ite_true]; exact hpl⟩
  · intro i th' d e x k n hi hd hx
    obtain ⟨rfl, rfl⟩ := hs1 hi
    simp only [witS, ite_true] at hx
    rcases d with _ | d
    · cases hx
    · simp only [frameTerms, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact himm d f x k n hf hx
  · intro q hq m' hg
    rw [hown q m' hg]
    exact ⟨th, by rw [hth]; rfl, hq⟩

/-- **`Components` for a one-thread pair at `PlacedSE`**: `components_oneS`
at `PlacedS`, `components_oneSE` at the output extern's model. -/
theorem components_oneSX (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat} {rS : Range} {Tk : State → Prop}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl) (hh : HeldOk Λ rS Tk th.st hl)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0]) (hpl : PlacedSE Λ lbl th.st (Ctl.of th0) th0.stack)
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  rcases hpl with hpl | ⟨hext, hfp⟩
  · exact components_oneS hwf hth hheld hh hmi hs0 hpl hinv hown
  · exact components_oneSE hwf hth hheld hh hmi hs0 hext hfp hinv hown

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.components_oneSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.components_oneSX
