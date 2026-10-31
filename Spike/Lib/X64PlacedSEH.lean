/-
**The held-range (`H`) variants of the x86-64 placement consumer**: the
x86-64 side of `Spike/Lib/A64PlacedSE.lean`'s and `Spike/Lib/A64ConsumerS.lean`'s
`…H` lemmas, which `Spike/Lib/X64PlacedSE.lean` and
`Spike/Lib/X64ConsumerS.lean` lack (partial-twin gap). Same
names, same namespaces as AArch64's (`X64ConsumerS`, `X64ConsumerA`), so a
later move into those files is a cut and paste.

- `stackRange_held`, `components_oneSH`: `Components` for a one-thread pair
  at `PlacedS` whose held ranges are thread 0's and owned (`HeldPathS.own`),
  in place of `HeldOk`.
- `PostSAH`, `post_progressSAH`: `PostSA` over a held predicate `H`.
- `components_oneSEH`, `components_oneSXH`: at `PlacedSE`.

The held hypothesis `hho` is discharged at the wake instance.
-/
import Spike.Lib.X64PlacedSE

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer

variable {Λ : Scc.Sem.Layout}

/-- **The stack range of a one-thread configuration** whose held ranges are
thread 0's and owned (`HeldPathS.own`): thread 0's, one of them, owned. -/
theorem stackRange_held {t : T.M.Cfg} {th : Thread isa} {hl : List (Nat × Range)} (hth : t.1.threads = #[th])
    (hheld : t.2.held = hl) (hho : ∀ x ∈ hl, x.1 = 0 ∧ Owned Λ x.2 th.st) {j : Nat} {rg : Range}
    (h : T.M.stackRange t j = some rg) : j = 0 ∧ Owned Λ rg th.st := by
  change Kernel.stackRangeOf abi t j = some rg at h
  unfold Kernel.stackRangeOf at h
  split at h
  · cases h
  · rename_i tt htt
    obtain ⟨rfl, rfl⟩ := get_one hth htt
    rw [hheld] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, (hho x (List.mem_of_find?_eq_some hx)).2⟩

/-- **`Components` for a one-thread pair at any depth, the held ranges
thread 0's and owned** (`components_oneS` over `HeldPathS.own`: the stack
range one of them, `stackRange_held`). -/
theorem components_oneSH (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl)
    (hho : ∀ x ∈ hl, x.1 = 0 ∧ Owned Λ x.2 th.st)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0]) (hpl : PlacedS Λ lbl th.st (Ctl.of th0) th0.stack)
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  obtain ⟨envm, hrep, htot, himm⟩ := hpl
  have hsr : ∀ j rg, T.M.stackRange t j = some rg → j = 0 ∧ Owned Λ rg th.st := fun j rg h =>
    stackRange_held hth hheld hho h
  have hs1 : ∀ {i} {th'}, s.ths[i]? = some th' → i = 0 ∧ th' = th0 := by
    intro i th' h
    rw [hs0] at h
    rcases i with _ | i
    · exact ⟨rfl, (Option.some.inj h).symm⟩
    · simp at h
  refine ⟨witS lbl lsize ts envm t.1.mem.last, Components.ofMemRelP (tp := []) (sp := []) hinv.mem
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := (fun j rg h => by obtain ⟨-, ho⟩ := hsr j rg h; exact ho.1),
      stack_disj := (fun j j' rg rg' hne h h' => absurd ((hsr j rg h).1.trans (hsr j' rg' h').1.symm) hne),
      stack_owned := (fun j rg h j' tt' htt a h8 h1 h2 => by
        obtain ⟨rfl, ho⟩ := hsr j rg h
        obtain ⟨rfl, rfl⟩ := get_one hth htt
        exact ⟨fun _ => rfl, fun _ => ho.2 a h8 h1 h2⟩),
      stack_private := (fun j rg h m hm hc => by
        obtain ⟨-, ho⟩ := hsr j rg h
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
    simp only [witS] at hwp
    exact hrep d e hd x ty ws hx k wd wp hwd hwp
  · intro i th' hi d e xs hd hxs _hxf x hx ty ws hl k hk
    obtain ⟨rfl, rfl⟩ := hs1 hi
    obtain ⟨pl, hpl⟩ := htot d e xs hd hxs x hx ty ws hl k hk
    exact ⟨pl, by simp only [witS]; exact hpl⟩
  · intro i th' d e x k n hi hd hx
    obtain ⟨rfl, rfl⟩ := hs1 hi
    simp only [witS] at hx
    exact himm d e x k n hd hx
  · intro q hq m' hg
    rw [hown q m' hg]
    exact ⟨th, by rw [hth]; rfl, hq⟩

/-- **After the exit** at any depth, the frames at `PlacedSE`, the ranges
held by `H` (`PostSA` over a held predicate, `HeldPathS`). -/
def PostSAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (H : State → List (Nat × Range) → Prop)
    (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (o : Outcome),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = { KS E Λ j hl pm with exited := some o }) ∧ (∀ a, Kernel.byte pm a = 0) ∧
    H th.st hl ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    PlacedSE Λ lbl th.st (Ctl.of th0) th0.stack ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧ OwnMsgs t.1.mem ∧
    MemIn Λ t.1.mem ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **There is progress after the exit** (`post_progressSA` at `PostSAH`). -/
theorem post_progressSAH {P : SrcSem.SrcParams} {p : Prog} {μ : Marks} {H : State → List (Nat × Range) → Prop}
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PostSAH Λ P p H t s) : T.M.Progress μ t := by
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
output extern's model, the held ranges thread 0's and owned**
(`components_oneSH` with the current frame unplaced): its term is a model
term (`ExternFrame`, exempt from `env_rep` and `env_total`) or reads no variable; the suspended frames by `FramesPlaced`. -/
theorem components_oneSEH (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl)
    (hho : ∀ x ∈ hl, x.1 = 0 ∧ Owned Λ x.2 th.st)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0])
    (hext : th0.term ∈ externModelTerms ∨ exprFv th0.term = []) (hpl : FramesPlaced Λ lbl th.st th0.stack)
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  obtain ⟨envf, hrep, htot, himm⟩ := hpl
  let envm : Nat → String → Nat → Option (WordPlace T.M.I.RegId) := fun d => match d with
    | 0 => fun _ _ => none
    | d + 1 => envf d
  have hsr : ∀ j rg, T.M.stackRange t j = some rg → j = 0 ∧ Owned Λ rg th.st := fun j rg h =>
    stackRange_held hth hheld hho h
  have hs1 : ∀ {i} {th'}, s.ths[i]? = some th' → i = 0 ∧ th' = th0 := by
    intro i th' h
    rw [hs0] at h
    rcases i with _ | i
    · exact ⟨rfl, (Option.some.inj h).symm⟩
    · simp at h
  refine ⟨witS lbl lsize ts envm t.1.mem.last, Components.ofMemRelP (tp := []) (sp := []) hinv.mem
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := (fun j rg h => by obtain ⟨-, ho⟩ := hsr j rg h; exact ho.1),
      stack_disj := (fun j j' rg rg' hne h h' => absurd ((hsr j rg h).1.trans (hsr j' rg' h').1.symm) hne),
      stack_owned := (fun j rg h j' tt' htt a h8 h1 h2 => by
        obtain ⟨rfl, ho⟩ := hsr j rg h
        obtain ⟨rfl, rfl⟩ := get_one hth htt
        exact ⟨fun _ => rfl, fun _ => ho.2 a h8 h1 h2⟩),
      stack_private := (fun j rg h m hm hc => by
        obtain ⟨-, ho⟩ := hsr j rg h
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

/-- **`Components` for a one-thread pair at `PlacedSE`, the held ranges
thread 0's and owned** (`components_oneSX` over `HeldPathS.own`). -/
theorem components_oneSXH (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl)
    (hho : ∀ x ∈ hl, x.1 = 0 ∧ Owned Λ x.2 th.st)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0]) (hpl : PlacedSE Λ lbl th.st (Ctl.of th0) th0.stack)
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  rcases hpl with hpl | ⟨hext, hfp⟩
  · exact components_oneSH hwf hth hheld hho hmi hs0 hpl hinv hown
  · exact components_oneSEH hwf hth hheld hho hmi hs0 hext hfp hinv hown

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.components_oneSXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.components_oneSXH
