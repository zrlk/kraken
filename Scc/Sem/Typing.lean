/-
**Typing invariants of the relation** (`Scc/DESIGN.md` §10): the facts
about source values that the per-construct proofs need and that the
memory and register relations do not give, because `ValRep` of `undef`
holds of every word.

- *Number operands at checked arithmetic* (`ThreadTyped.add_num`): the
  operands of `let x = a + b` are numbers, so the target's carry is the
  source's sum crossing `2^64`, and an overflow abort is justified.
- *Defined values at tests* (`ThreadTyped.ifeq_num`, `ThreadTyped.parity_num`,
  `ThreadTyped.ifnull_def`): an `ifeq` test reads numbers (or two thread-id
  references), a `parity` test reads numbers and an
  `ifnull` test reads `null` or a location, never `undef` (on which the
  source has no successor while the target branches).
- *No big number* (`NoBigNumT`, the overflow part of the budget): a step
  keeps it when every word it newly binds is small (`NoBigNumT.of_frames`,
  `NoBigNumT.push`). A word is small when some 64-bit word represents it
  (`small_of_valRep`), so a number loaded from memory is small under the
  memory relation (`MemRel.small`), and so is the result of a checked
  operation on its fall-through edge. A literal is small when below `2^64`.

The first two are WeakCore's typing: a thread is `ThreadTyped` when some
context types its term (`CoreTyping.Typed`) and its environment realises
the context's variables (`TermSound.FInv`), which WeakCore's token
soundness theorem gives at every reachable configuration
(`TermMain.machine_tokens_mainF`, `SpawnArmZ.machine_tokens_main_spawn`:
the `FInvR` conjunct). That theorem is not used here: its hypotheses
include WeakCore's assumed certification obligations, so for now the
segments carry these facts for their constructs (§10). Integer types are realised by one number
(`vr_intOf`). Representable locations (a location word's label placed and
its offset in bounds) need WeakCore's per-state cell-type map and are not
here.
-/
import Scc.Sem.MemRel
import WeakCore.TermSound

namespace Scc.Sem

open CoreLang CoreTerm CoreTyping TermRun TermSound

/-! ## Small words and `NoBigNumT` -/

/-- **A small word**: if it is a number, the number fits in 64 bits. -/
def Small (w : TermRun.Word) : Prop := ∀ n, w.val = .num n → n < 2 ^ 64

/-- A word some target word represents is small. -/
theorem small_of_valRep {lbl : WeakMem.AllocLabel → Option Nat} {w : TermRun.Word} {v : Nat}
    (h : ValRep lbl w.val v) : Small w := by
  intro n hn; rw [hn] at h; exact h.1

/-- A literal below `2^64` is small. -/
theorem small_cst {n : Nat} (h : n < 2 ^ 64) : Small (cst (.num n)) := by
  intro m hm; simp [cst, Promises.TVal.mk0] at hm; omega

/-- **Under the memory relation every number in source memory is small**
(`mem_rep` represents it by a target word). -/
theorem MemRel.small {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {pairs : List Nat}
    (h : MemRel Λ lbl lsize ts tm sm pairs) {k : Nat} {m : WeakMem.Msg} (hk : sm[k]? = some m) {n : Nat}
    (hn : m.val = .num n) : n < 2 ^ 64 := by
  obtain ⟨_, _, _, _, _, _, hv⟩ := h.mem_rep k m hk
  rw [hn] at hv; exact hv.1

/-- `NoBigNumT` is "every word of every frame of thread `i` is small". -/
theorem noBigNumT_iff {i : Nat} {s : TermRun.Cfg} :
    NoBigNumT i s ↔ ∀ th, s.ths[i]? = some th → ∀ e ∈ frameEnvs th, ∀ b ∈ e, ∀ w ∈ b.2.2, Small w :=
  Iff.rfl

/-- **A step keeps `NoBigNumT`** when every word in the new frames of thread
`i` was in its old frames or is small. -/
theorem NoBigNumT.of_frames {i : Nat} {s s' : TermRun.Cfg} {th th' : TermRun.TTh} (h : NoBigNumT i s)
    (hi : s.ths[i]? = some th) (hi' : s'.ths[i]? = some th')
    (hw : ∀ e ∈ frameEnvs th', ∀ b ∈ e, ∀ w ∈ b.2.2,
      (∃ e0 ∈ frameEnvs th, ∃ b0 ∈ e0, w ∈ b0.2.2) ∨ Small w) : NoBigNumT i s' := by
  intro t ht e he b hb w hw' n hn
  rw [hi'] at ht; cases ht
  rcases hw e he b hb w hw' with ⟨e0, he0, b0, hb0, hw0⟩ | hs
  · exact h th hi e0 he0 b0 hb0 w hw0 n hn
  · exact hs n hn

/-- **A binding keeps `NoBigNumT`**: thread `i` pushes a binding of small
words on its current frame, its suspended frames unchanged. -/
theorem NoBigNumT.push {i : Nat} {s s' : TermRun.Cfg} {th th' : TermRun.TTh} (h : NoBigNumT i s)
    (hi : s.ths[i]? = some th) (hi' : s'.ths[i]? = some th') {x : String} {ty : Ty} {ws : List TermRun.Word}
    (henv : th'.env = (x, ty, ws) :: th.env) (hst : th'.stack = th.stack) (hws : ∀ w ∈ ws, Small w) :
    NoBigNumT i s' := by
  refine h.of_frames hi hi' fun e he b hb w hw => ?_
  simp only [frameEnvs, List.mem_cons, hst] at he
  rcases he with rfl | he
  · rw [henv, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact .inr (hws w hw)
    · exact .inl ⟨th.env, by simp [frameEnvs], b, hb, hw⟩
  · exact .inl ⟨e, by simp [frameEnvs, he], b, hb, hw⟩

/-- `NoBigNumT i` depends only on thread `i`. -/
theorem NoBigNumT.of_eq {i : Nat} {s s' : TermRun.Cfg} (h : NoBigNumT i s) (he : s'.ths[i]? = s.ths[i]?) :
    NoBigNumT i s' := by
  intro th ht; rw [he] at ht; exact h th ht

/-! ## WeakCore's typing -/

/-- **A typed source thread** (the typing part of WeakCore's per-thread
invariant, `FInvR`'s `FInv` with `Typed`): some context `cx` types the
thread's term, and its current environment realises `cx`'s variables. -/
def ThreadTyped (p : Prog) (th : TermRun.TTh) : Prop :=
  ∃ ρ η K cx, Typed p cx th.term ∧ FInv ρ η th.σs K cx th.env

/-- **Every thread of the configuration is typed.** -/
def SrcTyped (p : Prog) (s : TermRun.Cfg) : Prop := ∀ (i : Nat) th, s.ths[i]? = some th → ThreadTyped p th

/-- **WeakCore's per-thread conclusion gives `ThreadTyped`**: the conjuncts
`Typed p cx th.term` and `FInvR … cx th.env Rf` of
`machine_tokens_mainF`/`machine_tokens_main_spawn`. -/
theorem threadTyped_of {p : Prog} {th : TermRun.TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {K : TEnv → Nat → List TermRun.Word → Res → Prop} {Rf : Res} (ht : Typed p cx th.term)
    (hf : FInvR ρ η th.σs K cx th.env Rf) : ThreadTyped p th :=
  ⟨ρ, η, _, cx, ht, hf.1⟩

/-- An integer type is realised by one number. -/
theorem vr_intOf {ρ : Nat → Nat} {η : TEnv} : ∀ {t : Ty} {o : Option Idx} {rt : Shp} {ws : List TermRun.Word},
    intOf t = some o → VR ρ η t rt ws → ∃ n, ws.map (·.val) = [.num n]
  | .intS _, _, _, _, _, h => ⟨_, h⟩
  | .int, _, _, _, _, h => h
  | .refine t _, o, _, _, ho, h => vr_intOf (t := t) (o := o) ho h.1

/-- An atom whose type (`peek`) is the type `t` evaluates to words that
realise `t`, in an environment realising the context. -/
theorem atom_vr {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : TermRun.Env}
    (hv : VarsOK ρ η σs cx.vars env) {x : String} {t : Ty} (hp : cx.peek (.var x) = .ok t) {rt : Ty}
    {ws : List TermRun.Word} (he : evalAt env (.var x) = some (rt, ws)) : VR ρ η t (shp rt) ws := by
  simp only [Cx.peek, Cx.find] at hp
  split at hp
  · rename_i y t' b hf
    have htt : t' = t := by
      cases b <;> simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    subst htt
    obtain ⟨rt', ws', hl, hvr, -⟩ := hv x _ hf
    simp only [evalAt] at he
    rw [hl] at he; cases he
    exact hvr
  · cases hp

/-- **An atom of integer type evaluates to one number**, in an environment
realising the context. -/
theorem atom_num {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : TermRun.Env}
    (hv : VarsOK ρ η σs cx.vars env) {a : At} {t : Ty} {o : Option Idx} (hp : cx.peek a = .ok t)
    (ho : intOf t = some o) {rt : Ty} {ws : List TermRun.Word} (he : evalAt env a = some (rt, ws)) :
    ∃ n, ws.map (·.val) = [.num n] := by
  cases a with
  | lit n => simp [evalAt] at he; obtain ⟨-, rfl⟩ := he; exact ⟨n, rfl⟩
  | unit => simp [Cx.peek] at hp; cases hp; simp [intOf] at ho
  | var x => exact vr_intOf ho (atom_vr hv hp he)

/-- One number, as a single word. -/
theorem num_of_map {ws : List TermRun.Word} {w : TermRun.Word} {n : Nat} (hw : ws = [w])
    (h : ws.map (·.val) = [.num n]) : w.val = .num n := by
  subst hw; simpa using h

namespace ThreadTyped

variable {p : Prog} {th : TermRun.TTh}

/-- **Number operands at checked arithmetic**: in a typed thread at
`let x = a + b in e`, each operand that evaluates to one word is a
number. -/
theorem add_num (h : ThreadTyped p th) {x : String} {a b : At} {e : Expr} (ht : th.term = .let_ x (.add a b) e)
    {c : At} (hc : c = a ∨ c = b) {rt : Ty} {w : TermRun.Word} (he : evalAt th.env c = some (rt, [w])) :
    ∃ n, w.val = .num n := by
  obtain ⟨ρ, η, K, cx, hty, hf⟩ := h
  rw [ht] at hty
  cases hty with
  | let_ hop _ =>
    have hv := hf.2.1
    cases hop with
    | addS hpa hpb hia hib _ =>
      rcases hc with rfl | rfl
      · obtain ⟨n, hn⟩ := atom_num hv hpa hia he; exact ⟨n, num_of_map rfl hn⟩
      · obtain ⟨n, hn⟩ := atom_num hv hpb hib he; exact ⟨n, num_of_map rfl hn⟩
    | addI hpa hpb hia hib _ =>
      rcases hc with rfl | rfl
      · obtain ⟨n, hn⟩ := atom_num hv hpa hia he; exact ⟨n, num_of_map rfl hn⟩
      · obtain ⟨n, hn⟩ := atom_num hv hpb hib he; exact ⟨n, num_of_map rfl hn⟩

/-- **Defined values at `ifeq`**: in a typed thread at `ifeq a b yes no`,
each operand that evaluates to one word is a number, or, when both operands
are `ThreadId`s (WeakCore's `PlainEq` admits that comparison), the reference
to a thread's id box; never `undef`. -/
theorem ifeq_num (h : ThreadTyped p th) {a b : At} {yes no : Expr} (ht : th.term = .ifeq a b yes no)
    {c : At} (hc : c = a ∨ c = b) {rt : Ty} {w : TermRun.Word} (he : evalAt th.env c = some (rt, [w])) :
    (∃ n, w.val = .num n) ∨ ∃ l, w.val = .loc ⟨l, 0⟩ 0 := by
  obtain ⟨ρ, η, K, cx, hty, hf⟩ := h
  have hv := hf.2.1
  have key : ∀ {t : Ty} {o : Option Idx}, cx.peek c = .ok t → intOf t = some o →
      (∃ n, w.val = .num n) ∨ ∃ l, w.val = .loc ⟨l, 0⟩ 0 :=
    fun hp ho => by obtain ⟨n, hn⟩ := atom_num hv hp ho he; exact .inl ⟨n, num_of_map rfl hn⟩
  have keyT : ∀ {t : Ty}, cx.peek c = .ok t → tidOf t = true →
      (∃ n, w.val = .num n) ∨ ∃ l, w.val = .loc ⟨l, 0⟩ 0 := by
    intro t hp ht'
    cases t <;> simp [tidOf] at ht'
    cases c with
    | lit n => simp [Cx.peek] at hp
    | unit => simp [Cx.peek] at hp
    | var x =>
      have hvr := atom_vr hv hp he
      simp only [VR] at hvr
      obtain ⟨l, -, hl, -⟩ := hvr
      exact .inr ⟨l, by simpa using hl⟩
  rw [ht] at hty
  cases hty with
  | ifeqPlain hpe _ _ =>
    obtain ⟨ta, tb, hpa, hpb, hab⟩ := hpe
    rcases hab with ⟨hia, hib, -⟩ | ⟨hta, htb⟩
    · rcases hc with rfl | rfl
      · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hia; exact key hpa ho
      · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hib; exact key hpb ho
    · rcases hc with rfl | rfl
      · exact keyT hpa hta
      · exact keyT hpb htb
  | ifeq hia hib _ _ _ =>
    rcases hc with rfl | rfl
    · obtain ⟨t, hp, ho⟩ := hia; exact key hp ho
    · obtain ⟨t, hp, ho⟩ := hib; exact key hp ho
  | ifeqRec hia hib _ _ _ _ =>
    rcases hc with rfl | rfl
    · obtain ⟨t, hp, ho⟩ := hia; exact key hp ho
    · obtain ⟨t, hp, ho⟩ := hib; exact key hp ho
  | ifeqZero hia hib _ _ _ _ =>
    rcases hc with rfl | rfl
    · obtain ⟨t, hp, ho⟩ := hia; exact key hp ho
    · obtain ⟨t, hp, ho⟩ := hib; exact key hp ho

/-- **Defined values at `parity`**: the tested operand is a number. -/
theorem parity_num (h : ThreadTyped p th) {a : At} {k : String} {ev od : Expr} (ht : th.term = .parity a k ev od)
    {rt : Ty} {w : TermRun.Word} (he : evalAt th.env a = some (rt, [w])) : ∃ n, w.val = .num n := by
  obtain ⟨ρ, η, K, cx, hty, hf⟩ := h
  rw [ht] at hty
  cases hty with
  | parity hi _ _ _ =>
    obtain ⟨t, hp, ho⟩ := hi
    obtain ⟨n, hn⟩ := atom_num hf.2.1 hp ho he
    exact ⟨n, num_of_map rfl hn⟩

/-- `use` types an atom as `peek` does. -/
theorem peek_of_use {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) : cx.peek a = .ok t := by
  unfold Cx.use at h
  cases hp : cx.peek a with
  | error m => rw [hp] at h; cases h
  | ok t' =>
    rw [hp] at h
    have : t' = t := by
      cases a <;> simp only [bind, Except.bind] at h <;> (try split at h) <;>
        simp_all [pure, Except.pure]
    rw [this]

/-- **Defined values at `ifnull`**: the tested operand, a variable of
optional-reference type, is `null` or a location. -/
theorem ifnull_def (h : ThreadTyped p th) {a : At} {y : String} {e₁ e₂ : Expr} (ht : th.term = .ifnull a e₁ y e₂)
    {rt : Ty} {w : TermRun.Word} (he : evalAt th.env a = some (rt, [w])) :
    w.val = .null ∨ ∃ l g, w.val = .loc l g := by
  obtain ⟨ρ, η, K, cx, hty, hf⟩ := h
  rw [ht] at hty
  cases hty with
  | ifnull hu _ _ _ =>
    have hp := peek_of_use hu
    cases a with
    | lit n => simp [Cx.peek] at hp
    | unit => simp [Cx.peek] at hp
    | var x =>
      have hvr := atom_vr hf.2.1 hp he
      simp only [VR] at hvr
      rcases hvr with hn | ⟨l, c, hl, -⟩
      · exact .inl (by simpa using hn)
      · exact .inr ⟨l, 0, by simpa using hl⟩

end ThreadTyped

end Scc.Sem
