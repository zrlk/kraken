/-
**Stage 3: weak fairness gives weak fairness
for instruction steps, at a fixed certification fuel.** ISA-neutral,
program-independent.

`WeakFair` (`LiveTrace.lean`) counts a promise step as a step of its
thread; `WeakFairInstr` asks for instruction steps. A thread that is
instruction-enabled from some point on and scheduled infinitely often might
a priori be scheduled only through promise steps. It cannot, because
`succs` certifies a promise with a *bounded* run: a promise step of `tid`
from `c` at fuel `fuel` needs a promise-free run of `tid` alone with at most
`fuel` instructions that empties its promise set (`CertOkN`,
`succs_casesN`). If every instruction step of the thread drops at most `B`
outstanding promises (`DropBounded`), that run fulfils at most `fuel * B`
of them, so a thread with more than `fuel * B` outstanding promises takes
no promise step (`prom_le_of_promiseStep`). A promise step adds one promise;
steps of other threads leave the thread alone; so a thread cannot take
infinitely many promise steps in a row (`weakFairInstr_of_weakFair`).

- `ThreadNPn`/`CertOkN`: runs of at most `n` instructions; certification
  within `n` instructions.
- `certify_writes_certOkN`: a write reported by `certify … fuel` comes with
  a certification within `fuel` instructions (the fuel-indexed companion of
  `PromiseSafe.certify_sound`; same proof shape, own invariant).
- `succs_casesN`: every successor is an instruction step, or a promise of a
  thread that certifies within `fuel` instructions.
- `DropBounded A B tid t`: on every run of `tid` alone from `t` (any
  memory), each instruction step drops at most `B` promises. A *semantic*
  hypothesis about the thread's program: no ISA-level bound holds in
  general (an `EvTree` path may contain any number of stores; on AArch64 an
  invalid layout can place many store cells at one address).
- **`weakFairInstr_of_weakFair`**: on a stuttering trace whose threads are
  all `DropBounded A B`, `WeakFair → WeakFairInstr`.
-/
import Kraken.Promising.LiveTrace
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising.Live

open Kraken.Promising

variable {I : ISA}

/-! ## Bounded runs and bounded certification -/

/-- Promise-free runs of thread `tid` alone with at most `n` instructions. -/
inductive ThreadNPn (A : Arch) (tid : Nat) : Nat → Thread I × Memory → Thread I × Memory → Prop
  | refl (n : Nat) (p : Thread I × Memory) : ThreadNPn A tid n p p
  | step {n : Nat} {p q r : Thread I × Memory} : ThreadStep A tid p q → ThreadNPn A tid n q r →
      ThreadNPn A tid (n + 1) p r

theorem ThreadNPn.mono {A : Arch} {tid : Nat} {n m : Nat} {p q : Thread I × Memory} (h : ThreadNPn A tid n p q)
    (hm : n ≤ m) : ThreadNPn A tid m p q := by
  induction h generalizing m with
  | refl => exact .refl _ _
  | @step n p q r hs _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .step hs (ih (by omega))

theorem ThreadNPn.tail {A : Arch} {tid : Nat} {n : Nat} {p q r : Thread I × Memory} (h : ThreadNPn A tid n p q)
    (hs : ThreadStep A tid q r) : ThreadNPn A tid (n + 1) p r := by
  induction h with
  | refl n p => exact .step hs (.refl _ _)
  | step h₁ _ ih => exact .step h₁ (ih hs)

/-- Thread `tid` empties its promise set within `n` instructions. -/
def CertOkN (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (n : Nat) : Prop :=
  ∃ t' mem', ThreadNPn A tid n (t, mem) (t', mem') ∧ t'.prom = []

/-! ## `certify` reports writes only for certifications within its fuel -/

private theorem foldl_invN {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => foldl_invN P f l (f b a) (hs b a List.mem_cons_self h0)
      (fun b' a' ha' => hs b' a' (List.mem_cons_of_mem _ ha'))

private theorem fold_thenN {α β : Type} {P Q : β → Prop} (f : β → α → β) (l : List α) (b : β) (h0 : P b)
    (hs : ∀ b a, a ∈ l → P b → P (f b a)) (hQ : ∀ b, P b → Q b) : Q (l.foldl f b) :=
  hQ _ (foldl_invN P f l b h0 hs)

/-- A certification result whose writes come with a certification within
`fuel` instructions. -/
def _root_.Kraken.Promising.CertResult.SoundN (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (fuel : Nat) (r : CertResult I) :
    Prop :=
  r.writes ≠ [] → CertOkN A tid t mem fuel

/-- An entry of `certify.go` with budget `n` left, from `(t0, mem0)` with
budget `fuel`: reached by at most `fuel - n` instructions, and a
certification within `fuel` exists once the entry is `done`. -/
def GoEntryN (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory) (fuel n : Nat)
    (e : Thread I × Memory × List (Msg × View) × Bool) : Prop :=
  (∃ k, k + n ≤ fuel ∧ ThreadNPn A tid k (t0, mem0) (e.1, e.2.1)) ∧ (e.2.2.2 = true → CertOkN A tid t0 mem0 fuel)

theorem certify_go_soundN (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory) (fuel : Nat) :
    ∀ (n : Nat) (s : Std.HashSet (Thread I × Memory) × CertResult I) (e : Thread I × Memory × List (Msg × View) × Bool),
      GoEntryN A tid t0 mem0 fuel n e → s.2.SoundN A tid t0 mem0 fuel →
        (certify.go A tid n s e).2.SoundN A tid t0 mem0 fuel := by
  intro n
  induction n with
  | zero =>
    rintro ⟨visited, acc⟩ ⟨t, mem, ws, done⟩ he hs
    rw [certify.go]
    split
    · exact hs
    dsimp only
    split
    · exact hs
    obtain ⟨⟨k, hk, hrun⟩, -⟩ := he
    by_cases hc : (!done && t.prom.isEmpty) = true
    · rw [ite_eq_left hc]
      have hok : CertOkN A tid t0 mem0 fuel := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_iff] at hc
        exact ⟨t, mem, hrun.mono (by omega), hc.2⟩
      dsimp only
      split <;> exact fun _ => hok
    · rw [ite_eq_right hc]
      dsimp only
      split <;> exact hs
  | succ n ih =>
    rintro ⟨visited, acc⟩ ⟨t, mem, ws, done⟩ he hs
    rw [certify.go]
    split
    · exact hs
    dsimp only
    split
    · exact hs
    obtain ⟨⟨k, hk, hrun⟩, hdone⟩ := he
    -- after the certification check: `acc1`, `done1`
    have key : ∀ (acc1 : CertResult I) (done1 : Bool), acc1.SoundN A tid t0 mem0 fuel →
        (done1 = true → CertOkN A tid t0 mem0 fuel) →
        CertResult.SoundN A tid t0 mem0 fuel
          (if t.halted = true then (visited.insert (t, mem), acc1)
           else match stepOne A t tid mem with
            | none => (visited.insert (t, mem), acc1)
            | some outs =>
              let x := outs.foldl (init := ([], acc1)) fun (next, acc) o =>
                match o with
                | .error m => (next, { acc with faults := acc.faults ++ [m] })
                | .ok o =>
                  if done1 then ((o.thread, o.mem, [], true) :: next, { acc with writes := acc.writes ++ o.promisedNow })
                  else ((o.thread, o.mem, ws ++ o.promisedNow, false) :: next, acc)
              x.1.foldl (certify.go A tid n) (visited.insert (t, mem), x.2)).2 := by
      intro acc1 done1 hs1 hd1
      split
      · exact hs1
      split
      · exact hs1
      rename_i outs hstep
      refine fold_thenN (P := fun R : List (Thread I × Memory × List (Msg × View) × Bool) × CertResult I =>
          (∀ e ∈ R.1, GoEntryN A tid t0 mem0 fuel n e) ∧ R.2.SoundN A tid t0 mem0 fuel)
        (Q := fun R => CertResult.SoundN A tid t0 mem0 fuel
          (List.foldl (certify.go A tid n) (visited.insert (t, mem), R.2) R.1).2)
        _ outs _ ⟨fun _ h => by simp at h, hs1⟩ ?_ ?_
      · rintro ⟨next, acc⟩ o ho ⟨hn, ha⟩
        cases o with
        | error m => exact ⟨hn, ha⟩
        | ok o =>
          have hrun' : ThreadNPn A tid (k + 1) (t0, mem0) (o.thread, o.mem) := hrun.tail ⟨outs, o, hstep, ho, rfl⟩
          dsimp only
          split
          · rename_i hd
            refine ⟨fun e he' => ?_, fun _ => hd1 hd⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · exact ⟨⟨k + 1, by omega, hrun'⟩, fun _ => hd1 hd⟩
            · exact hn e he'
          · refine ⟨fun e he' => ?_, ha⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · exact ⟨⟨k + 1, by omega, hrun'⟩, fun h => by cases h⟩
            · exact hn e he'
      · rintro ⟨next, acc⟩ ⟨hn, ha⟩
        exact foldl_invN (fun s : Std.HashSet (Thread I × Memory) × CertResult I => s.2.SoundN A tid t0 mem0 fuel)
          (certify.go A tid n) next _ ha (fun s e he' hs' => ih s e (hn e he') hs')
    by_cases hc : (!done && t.prom.isEmpty) = true
    · rw [ite_eq_left hc]
      have hok : CertOkN A tid t0 mem0 fuel := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_iff] at hc
        exact ⟨t, mem, hrun.mono (by omega), hc.2⟩
      exact key _ true (fun _ => hok) (fun _ => hok)
    · rw [ite_eq_right hc]
      exact key acc done hs hdone

/-- The cache is `SoundN` on the keys satisfying `K`. -/
def CacheSoundOnN (A : Arch) (K : Thread I → Nat → Prop) (fuel : Nat) (cache : CertCache I) : Prop :=
  ∀ (t : Thread I) (tid : Nat) (mem : Memory) (r : CertResult I),
    K t tid → cache[(t, tid, mem)]? = some r → r.SoundN A tid t mem fuel

private theorem prod_beq_iffN {α β : Type} [BEq α] [BEq β] (a b : α × β) :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show (a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true]

theorem certify_soundN [I.LawfulState] {A : Arch} {K : Thread I → Nat → Prop} (hK : KeyLawful K) {fuel : Nat}
    {cache : CertCache I} (hc : CacheSoundOnN A K fuel cache) {t : Thread I} {tid : Nat} (ht : K t tid)
    (mem : Memory) :
    (certify A cache t tid mem fuel).1.SoundN A tid t mem fuel ∧
      CacheSoundOnN A K fuel (certify A cache t tid mem fuel).2 := by
  unfold certify
  split
  · rename_i r h
    exact ⟨hc t tid mem r ht h, hc⟩
  · have hr := certify_go_soundN A tid t mem fuel fuel ({}, {}) (t, mem, [], false)
      ⟨⟨0, by omega, .refl _ _⟩, fun h => by cases h⟩ (fun h => absurd rfl h)
    refine ⟨hr, ?_⟩
    intro t' tid' mem' r' ht' h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i heq
      obtain ⟨h1, h23⟩ := (prod_beq_iffN _ _).mp heq
      obtain ⟨h2, h3⟩ := (prod_beq_iffN _ _).mp h23
      simp only [beq_iff_eq] at h2 h3
      subst h2 h3
      cases h
      rw [← hK t t' tid ht ht' h1]
      exact hr
    · exact hc t' tid' mem' r' ht' h

/-! ## Successors with bounded certification -/

/-- `SuccKind` with the certification bound: a promise of thread `tid`
needs `tid` to certify within `fuel` instructions. -/
inductive SuccKindN (A : Arch) (fuel : Nat) (c : Config I) : Config I → Prop
  | instr {tid : Nat} {t : Thread I} {outs : List (Except String (Outcome I))} {o : Outcome I} :
      c.threads[tid]? = some t → stepOne A t tid c.mem = some outs → .ok o ∈ outs →
      SuccKindN A fuel c (c.withThread tid o.thread o.mem)
  | promise {tid : Nat} {t : Thread I} {tnew : Time} {mem' : Memory} :
      c.threads[tid]? = some t → CertOkN A tid t c.mem fuel →
      SuccKindN A fuel c (c.withThread tid { t with prom := t.prom ++ [tnew] } mem')

theorem certifiedPromises_specN {A : Arch} [I.LawfulState] (cache : CertCache I) (c : Config I) (fuel : Nat)
    (hc : CacheSoundOnN A c.SameProg fuel cache) (tid : Nat) :
    CacheSoundOnN A c.SameProg fuel (certifiedPromises A cache c tid fuel).2.2 ∧
      ∀ y ∈ (certifiedPromises A cache c tid fuel).1, SuccKindN A fuel c y.1 := by
  unfold certifiedPromises
  split
  · exact ⟨hc, fun _ h => by cases h⟩
  · rename_i t ht
    obtain ⟨hw, hc'⟩ := certify_soundN (Config.SameProg.keyLawful c) hc ⟨t, ht, rfl⟩ c.mem
    refine ⟨hc', ?_⟩
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨w, hw', rfl⟩ := hy
    obtain ⟨p, hp, -⟩ := List.mem_map.mp (List.mem_eraseDups.mp hw')
    exact SuccKindN.promise ht (hw (List.ne_nil_of_mem (List.mem_filter.mp hp).1))

theorem succsL_specN {A : Arch} [I.LawfulState] {fuel : Nat} {mp : Option Nat} (c : Config I)
    (cache : CertCache I) (hc : CacheSoundOnN A c.SameProg fuel cache) :
    ∀ x ∈ (succsL A cache c fuel mp).1, SuccKindN A fuel c x.1 := by
  unfold succsL
  refine (foldl_invN (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
      CacheSoundOnN A c.SameProg fuel acc.2.2.2 ∧ ∀ x ∈ acc.1, SuccKindN A fuel c x.1) _ _ _
      ⟨hc, fun _ h => by cases h⟩ ?_).2
  rintro ⟨next, bound, faults, cache⟩ tid - ⟨hc, hn⟩
  have key : ∀ (F : List (Config I × List TraceEv) × Bool × List String × CertCache I)
      (ps : List (Config I × TraceEv)), (CacheSoundOnN A c.SameProg fuel F.2.2.2 ∧ ∀ x ∈ F.1, SuccKindN A fuel c x.1) →
      (∀ y ∈ ps, y ∈ (certifiedPromises A F.2.2.2 c tid fuel).1) →
      CacheSoundOnN A c.SameProg fuel (certifiedPromises A F.2.2.2 c tid fuel).2.2 ∧
        ∀ x ∈ F.1.reverse ++ List.map (fun x => (x.1, [x.2])) ps, SuccKindN A fuel c x.1 := by
    intro F ps ⟨hF, hF1⟩ hps
    obtain ⟨hc', hp'⟩ := certifiedPromises_specN _ c fuel hF tid
    refine ⟨hc', fun x hx => ?_⟩
    rcases List.mem_append.mp hx with h | h
    · exact hF1 x (List.mem_reverse.mp h)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact hp' y (hps y hy)
  have hsub : ∀ (ps : List (Config I × TraceEv)) (y : Config I × TraceEv),
      y ∈ (match mp, c.threads[tid]? with
        | some k, some t => if t.prom.length < k then ps else []
        | _, _ => ps) → y ∈ ps := by
    intro ps y hy
    split at hy
    · split at hy
      · exact hy
      · cases hy
    · exact hy
  simp only
  split
  · exact key _ _ ⟨hc, hn⟩ (hsub _)
  · rename_i outs hstep
    obtain ⟨t, ht, hstep⟩ := stepThread_eq_some hstep
    refine key _ _ (foldl_invN (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
        CacheSoundOnN A c.SameProg fuel acc.2.2.2 ∧ ∀ x ∈ acc.1, SuccKindN A fuel c x.1) _ _ _ ⟨hc, hn⟩ ?_) (hsub _)
    rintro ⟨next, bound, faults, cache⟩ o ho ⟨hc, hn⟩
    cases o with
    | error m => exact ⟨hc, hn⟩
    | ok o =>
      have hnew : SuccKindN A fuel c (c.withThread tid o.thread o.mem) := .instr ht hstep ho
      obtain ⟨-, hc'⟩ := certify_soundN (Config.SameProg.keyLawful c) hc ⟨t, ht, stepOne_static A hstep ho⟩ o.mem
      simp only
      split
      · refine ⟨hc, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnew
        · exact hn x hx
      · split
        · refine ⟨hc', fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hnew
          · exact hn x hx
        · exact ⟨hc', hn⟩

/-- **Every successor is an instruction step, or a promise of a thread that
certifies within `fuel` instructions.** -/
theorem succs_casesN {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : c' ∈ (succs A c fuel).1) : SuccKindN A fuel c c' := by
  unfold succs at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact succsL_specN c {} (fun _ _ _ _ _ h => by simp at h) x hx

/-! ## Bounded promise drop -/

/-- **Every instruction step of thread `tid` from `t` (on any run of `tid`
alone, against any memory) drops at most `B` outstanding promises.** -/
def DropBounded (A : Arch) (B tid : Nat) (t : Thread I) : Prop :=
  ∀ mem p q, ThreadNP A tid (t, mem) p → ThreadStep A tid p q → p.1.prom.length ≤ q.1.prom.length + B

/-- **A step invariant `S` of the thread state holds along a run of the
thread alone** (the shared skeleton of the `threadNP_sinv` lemmas). -/
theorem ThreadNP.stateInv {A : Arch} {tid : Nat} (S : I.State → Prop)
    (hS : ∀ {t : Thread I} {mem outs} {o : Outcome I}, S t.st → stepOne A t tid mem = some outs → .ok o ∈ outs →
      S o.thread.st) {p q : Thread I × Memory} (h : ThreadNP A tid p q) (hp : S p.1.st) : S q.1.st := by
  induction h with
  | refl => exact hp
  | step hs _ ih => obtain ⟨_, _, hs, ho, rfl⟩ := hs; exact ih (hS hp hs ho)

/-- **A step invariant whose steps drop at most `B` promises gives
`DropBounded`** (the shared skeleton of the `dropBounded_of_sinv`
lemmas). -/
theorem dropBounded_of_stateInv {A : Arch} {B tid : Nat} (S : I.State → Prop)
    (hS : ∀ {t : Thread I} {mem outs} {o : Outcome I}, S t.st → stepOne A t tid mem = some outs → .ok o ∈ outs →
      S o.thread.st ∧ t.prom.length ≤ o.thread.prom.length + B) {t : Thread I} (h : S t.st) :
    DropBounded A B tid t := by
  intro mem p q hr ⟨_, _, hs, ho, e⟩
  subst e
  exact (hS (ThreadNP.stateInv S (fun h hs ho => (hS h hs ho).1) hr h) hs ho).2

theorem ThreadNP.trans' {A : Arch} {tid : Nat} {p q r : Thread I × Memory} (h₁ : ThreadNP A tid p q)
    (h₂ : ThreadNP A tid q r) : ThreadNP A tid p r := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A run of at most `n` instructions from a `DropBounded` thread drops at
most `n * B` promises. -/
theorem ThreadNPn.prom_le {A : Arch} {B tid : Nat} {t : Thread I} {mem : Memory} (hd : DropBounded A B tid t) :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNP A tid (t, mem) p → ThreadNPn A tid n p q →
      p.1.prom.length ≤ q.1.prom.length + n * B := by
  intro n p q hp h
  induction h with
  | refl n p => exact Nat.le_add_right _ _
  | @step n p q r hs _ ih =>
    have h1 := hd mem p q hp hs
    have h2 := ih (hp.tail hs)
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **A thread with more than `fuel * B` outstanding promises makes no
promise**: a certification within `fuel` instructions fulfils at most
`fuel * B` of them. -/
theorem prom_le_of_certOkN {A : Arch} {B tid fuel : Nat} {t : Thread I} {mem : Memory}
    (hd : DropBounded A B tid t) (hc : CertOkN A tid t mem fuel) : t.prom.length ≤ fuel * B := by
  obtain ⟨t', mem', h, ht'⟩ := hc
  have := ThreadNPn.prom_le hd (.refl _) h
  simp only [ht', List.length_nil] at this
  omega

/-! ## Weak fairness for instruction steps -/

/-- Thread `tid`'s promise count at index `i` (`0` if absent). -/
def promCount (cfg : Nat → Config I) (tid i : Nat) : Nat :=
  ((cfg i).threads[tid]?.map (·.prom.length)).getD 0

/-- A step that is not an instruction step of `tid` either leaves `tid`'s
thread alone or is a promise of `tid` (from a thread with at most
`fuel * B` promises, adding one). -/
theorem step_cases_tid [I.LawfulState] {A : Arch} {fuel B : Nat} {c c' : Config I} {tid : Nat}
    (h : c' ∈ (succs A c fuel).1) (hni : ¬ InstrBy A tid c c')
    (hd : ∀ t, c.threads[tid]? = some t → DropBounded A B tid t) :
    c'.threads[tid]? = c.threads[tid]? ∨
      ∃ t, c.threads[tid]? = some t ∧ t.prom.length ≤ fuel * B ∧
        ∃ t', c'.threads[tid]? = some t' ∧ t'.prom.length = t.prom.length + 1 := by
  cases succs_casesN h with
  | @instr j t outs o hj hs ho =>
    by_cases hjt : j = tid
    · subst hjt; exact absurd ⟨t, outs, o, hj, hs, ho, rfl⟩ hni
    · left; rw [Config.withThread_get? c _ _ (lt_size_of_get? hj), ite_eq_right hjt]
  | @promise j t tnew mem' hj hc =>
    by_cases hjt : j = tid
    · subst hjt
      right
      refine ⟨t, hj, prom_le_of_certOkN (hd t hj) hc, { t with prom := t.prom ++ [tnew] }, ?_, by simp⟩
      rw [Config.withThread_get? c _ _ (lt_size_of_get? hj), ite_eq_left rfl]
    · left; rw [Config.withThread_get? c _ _ (lt_size_of_get? hj), ite_eq_right hjt]

/-- **Weak fairness gives weak fairness for instruction steps**, on a
stuttering trace whose threads drop at most `B` promises per instruction
(`DropBounded`), at any fuel: a thread that is instruction-enabled from some
point on takes instruction steps infinitely often. -/
theorem weakFairInstr_of_weakFair [I.LawfulState] {A : Arch} {fuel B : Nat} (tr : TraceS A fuel I)
    (hd : ∀ i tid t, (tr.cfg i).threads[tid]? = some t → DropBounded A B tid t)
    (hf : WeakFair A fuel tr.cfg) : WeakFairInstr A fuel tr.cfg := by
  intro tid ⟨n, hn⟩ m
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ j, max n m ≤ j → ¬ InstrScheduledAt A fuel tr.cfg tid j := fun j hj hs =>
    hno ⟨j, by omega, hs⟩
  -- every step from `max n m` on is in `succs` (no stutter: `tid` is enabled)
  have hsucc : ∀ j, n ≤ j → tr.cfg (j + 1) ∈ (succs A (tr.cfg j) fuel).1 := by
    intro j hj
    rcases tr.step j with h | ⟨hfin, -⟩
    · exact h
    · obtain ⟨c', h1, h2⟩ := hn j hj
      exact absurd ⟨c', h1, .inl h2⟩ (not_enabled_of_final hfin)
  -- the promise count never drops, and grows at every step scheduling `tid`
  have hstep : ∀ j, max n m ≤ j →
      promCount tr.cfg tid j ≤ promCount tr.cfg tid (j + 1) ∧
        (ScheduledAt A fuel tr.cfg tid j → promCount tr.cfg tid j ≤ fuel * B ∧
          promCount tr.cfg tid (j + 1) = promCount tr.cfg tid j + 1) := by
    intro j hj
    have hni : ¬ InstrBy A tid (tr.cfg j) (tr.cfg (j + 1)) := fun h =>
      hno' j hj ⟨hsucc j (by omega), h⟩
    rcases step_cases_tid (hsucc j (by omega)) hni (hd j tid) with heq | ⟨t, ht, hle, t', ht', hlen⟩
    · refine ⟨by rw [promCount, promCount, heq]; exact Nat.le_refl _, fun hs => ?_⟩
      rcases hs.2 with hi | ⟨t, p, ht, -, heq'⟩
      · exact absurd hi hni
      · exfalso
        rw [heq', Config.withThread_get? _ _ _ (lt_size_of_get? ht), ite_eq_left rfl, ht] at heq
        have := congrArg (fun o => Option.map (fun t : Thread I => t.prom.length) o) heq
        simp at this
    · have e1 : promCount tr.cfg tid j = t.prom.length := by simp [promCount, ht]
      have e2 : promCount tr.cfg tid (j + 1) = t'.prom.length := by simp [promCount, ht']
      rw [e1, e2, hlen]
      exact ⟨Nat.le_succ _, fun _ => ⟨hle, rfl⟩⟩
  -- infinitely many scheduled steps: the count exceeds `fuel * B`
  have hgrow : ∀ k, ∃ j, max n m ≤ j ∧ k ≤ promCount tr.cfg tid j := by
    intro k
    induction k with
    | zero => exact ⟨max n m, Nat.le_refl _, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨j, hj, hk⟩ := ih
      obtain ⟨j', hj', hs⟩ := hf tid ⟨n, fun i hi => let ⟨c', h1⟩ := hn i hi; ⟨c', h1.1, .inl h1.2⟩⟩ j
      have hmono : ∀ d, promCount tr.cfg tid j ≤ promCount tr.cfg tid (j + d) := by
        intro d
        induction d with
        | zero => exact Nat.le_refl _
        | succ d ihd => exact Nat.le_trans ihd (hstep (j + d) (by omega)).1
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
      refine ⟨j + d + 1, by omega, ?_⟩
      have := ((hstep (j + d) (by omega)).2 hs).2
      have := hmono d
      omega
  obtain ⟨j, hj, hk⟩ := hgrow (fuel * B + 1)
  obtain ⟨j', hj', hs⟩ := hf tid ⟨n, fun i hi => let ⟨c', h1⟩ := hn i hi; ⟨c', h1.1, .inl h1.2⟩⟩ j
  have hmono : ∀ d, promCount tr.cfg tid j ≤ promCount tr.cfg tid (j + d) := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ihd => exact Nat.le_trans ihd (hstep (j + d) (by omega)).1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  have := ((hstep (j + d) (by omega)).2 hs).1
  have := hmono d
  omega

end Kraken.Promising.Live

#print axioms Kraken.Promising.Live.weakFairInstr_of_weakFair
