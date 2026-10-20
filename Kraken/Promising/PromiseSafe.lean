/-
A restriction-free foundation for Stage 2: the architecture of Svendsen et al.,
*A separation logic for a
promising semantics* (ESOP 2018, "SLR"), transferred to Kraken's
Promising-ARM machine, and its simplest instance proved.

SLR proves its logic sound over the *full* promising machine. Promise steps
are handled once, by Theorem 1 (`npsafe ⇒ safe`), whose proof uses that a
certification run is a promise-free run of the same thread. No restriction on
programs is needed: racy programs get weaker conclusions, never none.

## Contents

- `ThreadStep`, `ThreadNP`: one instruction / a run of one thread alone
  against the memory, without promise steps (outstanding promises may be
  fulfilled): SLR's `−→NP`. `NPStep`, `NPReachable`: machine steps that are
  instruction steps; configurations may carry promises (unlike
  `ReachablePF`, which requires every configuration to be promise-free).
- `Ctx.Ext`, `runTree_ext`, `stepOne_ext`: an instruction's memory is the old
  memory with exactly its "promise now" writes (`promisedNow`) appended.
- `CertWrite`, `CertOk`, `CacheSound`, `CertifySound`: the specification of
  `certify` (Kraken's Lemma 1, below).
- `certify_go_sound`, `certify_sound`: `certify` meets it (it is a total
  function). `ISA.LawfulState`: what the memo table needs from
  `I.beqState`; instances for AArch64, x64 and Toy in `CertifyAArch64.lean`,
  `CertifyX64.lean`, `CertifyToy.lean`.
- `SuccKind`, `succsL_spec`, `succs_cases`: every `succs` successor is an
  instruction step or a promise of a `CertWrite`.
- The write-invariant instance (Kang et al. §5.5 in SLR's architecture):
  `MemInv`, `WritesPreserve`, `write_invariant_np` (runs without promise
  steps) and `write_invariant` (every `Reachable` configuration, promises
  included). Both are unconditional (`write_invariant` for any ISA with
  `ISA.LawfulState`).
- `ResModel`, `EnvExt`, `NPSafe`, `Safe`, `ResModel.Laws`,
  `NPSafeImpliesSafe`: SLR's Figs. 7–8 and Theorem 1 over Kraken, as `Prop`s.
- `Config.MachInv`, `Config.Unfulfils`, `ResModel.PromisedRelease`,
  `VirtualRel`, `NPSafeImpliesAdequateV`: Theorem 1′ (design (V), restated
  in and switched to option (B)),
  as a `Prop`.

## Kraken's Lemma 1

SLR's appendix Lemma 1: a promise followed by its certification run is a
promise-free run from the pre-promise configuration. Kraken *defines*
promises that way round: `certifiedPromises` runs `certify` on the
pre-promise thread and memory `(t, c.mem)` and offers the writes of its
certifying traces whose constraining view is `≤ |M|`, appended at `|M| + 1`.
So the direction SLR's Theorem 1 uses (the promised message is written by a
promise-free run of the thread alone from the pre-promise configuration,
`CertWrite`) holds by definition, and `succs_cases` exposes it.

That `certify` returns what its docstring says is a theorem about the
implementation, not about programs. `certify`'s search is a structural
recursion on the instruction budget, so it is a total function, and
`certify_go_sound` proves `CertResult.Sound` by induction on it ("every
entry is a `ThreadNP` state; `ws` are writes along its path";
`hasDeadPromise` and `visited` only prune). Its memo table is looked up by
`BEq`, which for AArch64 and x64 compares only the dynamic part of an ISA
state: `certify_sound` holds on any family of queries on which `==` is
equality, and the queries of one `succsL` call form one (`Config.SameProg`,
from `ISA.LawfulState`). `CertifySound` (every cache, every query) holds
when `beqState` is equality outright (`certifySound`: Toy).

The converse (the post-promise configuration is consistent: the same trace
with the promised write fulfilled at `|M| + 1` instead of performed at its
own fresh timestamp) is what makes the promise rule agree with Pulte et
al.'s, and it is *not* needed for Theorem 1 (SLR's proof uses only the
direction above). Its relation is a simulation, not an equality: the two
memories agree up to `|M|`; above it, the thread's own messages are the same
per location and in the same per-location order (between the promise and
its fulfilment the certifying trace writes no message to the promised
location: its `coh` would pass `|M| + 1`), with the promised message moved
from its fresh timestamp to `|M| + 1` and the intermediate ones shifted up by
one; views `≤ |M|` are equal and views above `|M|` are renamed accordingly.
-/
import Kraken.Promising.Conservative

namespace Kraken.Promising

variable {I : ISA}

/-! ## Contexts: an instruction appends exactly its "promise now" writes -/

/-- `c'` extends `c` by appending writes: the initial values are unchanged,
and the messages appended are exactly the writes recorded in `promisedNow`
since `c`. -/
structure Ctx.Ext (c c' : Ctx) : Prop where
  init : c'.mem.init = c.mem.init
  app : ∃ ws : List (Msg × View),
    c'.promisedNow = c.promisedNow ++ ws ∧ c'.mem.msgs.toList = c.mem.msgs.toList ++ ws.map (·.1)

theorem Ctx.Ext.refl (c : Ctx) : c.Ext c := ⟨rfl, [], by simp, by simp⟩

theorem Ctx.Ext.of_eq {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.promisedNow = c.promisedNow) : c.Ext c' :=
  ⟨by rw [hm], [], by simp [hp], by simp [hm]⟩

theorem Ctx.Ext.trans {c c' c'' : Ctx} (h₁ : c.Ext c') (h₂ : c'.Ext c'') : c.Ext c'' := by
  obtain ⟨hi₁, ws₁, hp₁, hm₁⟩ := h₁
  obtain ⟨hi₂, ws₂, hp₂, hm₂⟩ := h₂
  exact ⟨hi₂.trans hi₁, ws₁ ++ ws₂, by rw [hp₂, hp₁, List.append_assoc],
    by rw [hm₂, hm₁, List.map_append, List.append_assoc]⟩

private theorem ite_none_left {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

private theorem ite_none_right {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then y else none) = some x) : y = some x := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

private theorem mem_ite_nil {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α}
    (h : x ∈ (if p then ys else [])) : x ∈ ys := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_mp {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.2.2.mem = c.mem ∧ x.2.2.promisedNow = c.promisedNow := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem fenceStep_promisedNow (c : Ctx) (k : FenceKind) : (fenceStep c k).promisedNow = c.promisedNow := by
  cases k <;> rfl

theorem Ctx.Ext.fenceStep (c : Ctx) (k : FenceKind) : c.Ext (fenceStep c k) :=
  .of_eq (fenceStep_mem c k) (fenceStep_promisedNow c k)

theorem Ctx.Ext.fenceOpt (c : Ctx) (b : Bool) (k : FenceKind) :
    c.Ext (if b then Kraken.Promising.fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact .fenceStep c k

/-- The `fulfil` rule appends at most the "promise now" message, and records
it in `promisedNow`. -/
theorem writeSuccs_ext {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c.Ext c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, ht⟩ | h
  · split at ht
    · have h := ite_none_right ht
      simp only [Option.some.injEq] at h
      subst h
      exact .of_eq rfl rfl
    · cases ht
  · have h := mem_ite_nil h
    rw [List.mem_singleton] at h
    subst h
    refine ⟨rfl, [({ loc := l, val := v, tid }, _)], rfl, ?_⟩
    simp [afterWrite]

theorem runTree_ext {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.Ext c' := by
  induction tree with
  | done s0 =>
    intro c s c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl _
  | fault msg =>
    intro c s c' h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hi
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_mp A iv h0
    exact (Ctx.Ext.of_eq hm hp).trans (ih v c0 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_ext A tid _ hc0).trans (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have h' := ih false _ s c' h.2
      exact Ctx.Ext.trans (.of_eq (by rfl) (by rfl)) h'
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (Ctx.Ext.fenceStep c k).trans (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := Ctx.Ext.fenceOpt c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    obtain ⟨hm2, hp2⟩ := readSuccs_mp A iv h2
    have h12 : c.Ext c2 := h1.trans (.of_eq hm2 hp2)
    simp only at h
    split at h
    · exact (h12.trans (Ctx.Ext.fenceOpt c2 A.rmwFence .sy)).trans (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have h23 := writeSuccs_ext A tid _ hc3
      refine (h12.trans h23).trans (Ctx.Ext.trans ?_ (ih old _ s c' h))
      apply Ctx.Ext.trans _ (Ctx.Ext.fenceOpt _ A.rmwFence .sy)
      split
      · exact .of_eq rfl rfl
      · exact .of_eq rfl rfl

end Rules

/-- An instruction's memory is the old memory with exactly its "promise now"
writes appended. -/
theorem stepOne_ext (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    o.mem.init = mem.init ∧ o.mem.msgs.toList = mem.msgs.toList ++ o.promisedNow.map (·.1) := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, -, rfl⟩ := ho
      obtain ⟨hi, ws, hp, hm⟩ := runTree_ext A tid _ tree _ st c' hr
      simp only [List.nil_append] at hp
      exact ⟨hi, by simp only [hp]; exact hm⟩

/-! ## Promise-free runs of one thread -/

/-- One instruction of thread `tid`, run alone against `p.2`: a successful
outcome of `stepOne`. No promise step; an outstanding promise may be
fulfilled. This is SLR's `−→NP` for one thread. -/
def ThreadStep (A : Arch) (tid : Nat) (p q : Thread I × Memory) : Prop :=
  ∃ outs o, stepOne A p.1 tid p.2 = some outs ∧ .ok o ∈ outs ∧ q = (o.thread, o.mem)

/-- Promise-free runs of thread `tid` alone (`−→NP*`). -/
inductive ThreadNP (A : Arch) (tid : Nat) : Thread I × Memory → Thread I × Memory → Prop
  | refl (p : Thread I × Memory) : ThreadNP A tid p p
  | step {p q r : Thread I × Memory} : ThreadStep A tid p q → ThreadNP A tid q r → ThreadNP A tid p r

/-- A write `p` (message and constraining view) that thread `tid` performs as
"promise now" on some promise-free run from `(t, mem)`: what
`CertResult.writes` is documented to contain. -/
def CertWrite (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (p : Msg × View) : Prop :=
  ∃ t1 mem1 outs o, ThreadNP A tid (t, mem) (t1, mem1) ∧ stepOne A t1 tid mem1 = some outs ∧
    .ok o ∈ outs ∧ p ∈ o.promisedNow

/-- `certified` as documented: some promise-free run of the thread alone
empties its promise set (SLR's consistency, `P'(i) = ∅`). -/
def CertOk (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) : Prop :=
  ∃ t' mem', ThreadNP A tid (t, mem) (t', mem') ∧ t'.prom = []

/-- A certification result is sound for its key: it lists only writes of
promise-free runs, and claims `certified` only if the thread can empty its
promise set. -/
def CertResult.Sound (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (r : CertResult I) : Prop :=
  (∀ p ∈ r.writes, CertWrite A tid t mem p) ∧ (r.certified = true → CertOk A tid t mem)

/-- Every cached certification result is sound for its key. -/
def CacheSound (A : Arch) (cache : CertCache I) : Prop :=
  ∀ (t : Thread I) (tid : Nat) (mem : Memory) (r : CertResult I),
    cache[(t, tid, mem)]? = some r → r.Sound A tid t mem

/-- **Kraken's Lemma 1, as a specification of `certify`.** Every write
`certify` reports was performed on a promise-free run of the thread alone
from the configuration it was asked about, `certified` is only claimed when
such a run empties the promise set, and the cache stays sound.

This is the property `certify`'s docstring describes, for *every* cache and
query. It holds when `Thread`'s `==` is equality, i.e. when `I.beqState`
decides equality of whole ISA states (`certifySound`; the Toy ISA). It does
not hold in general for ISAs whose `beqState` compares only the dynamic part
of a state (AArch64, x64: the program, end address and declarations are not
compared): an arbitrary cache may hold an entry of one program that answers
a query about another with the same machine state. The
machine theorems therefore use the weaker, relative `certify_sound` below,
which holds for every ISA with `ISA.LawfulState` and suffices because within
one `succsL` call all queries of a thread id are about the same program. -/
def CertifySound (A : Arch) (I : ISA) : Prop :=
  ∀ (cache : CertCache I) (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat), CacheSound A cache →
    (certify A cache t tid mem fuel).1.Sound A tid t mem ∧ CacheSound A (certify A cache t tid mem fuel).2

private theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => foldl_inv P f l (f b a) (hs b a List.mem_cons_self h0)
      (fun b' a' ha' => hs b' a' (List.mem_cons_of_mem _ ha'))

private theorem fold_then {α β : Type} {P Q : β → Prop} (f : β → α → β) (l : List α) (b : β) (h0 : P b)
    (hs : ∀ b a, a ∈ l → P b → P (f b a)) (hQ : ∀ b, P b → Q b) : Q (l.foldl f b) :=
  hQ _ (foldl_inv P f l b h0 hs)

/-! ## `certify` is sound

`certify` is total (structural recursion on the instruction budget), so its
specification is a theorem. Two parts:

- the search (`certify.go`): every state it visits is reached from the root
  by a promise-free run (`ThreadNP`), and the writes it records are
  performed along such runs (`certify_go_sound`); `visited` and
  `hasDeadPromise` only prune, and `boundHit`/`faults` are not part of
  soundness;
- the memo table: a lookup returns the entry of any key `==` to the query.
  `ISA.LawfulState` says what `beqState` decides: equality of states with
  the same *static part* (program, layout). The cache is sound on any family
  of keys on which `==` is equality (`CacheSoundOn`, `KeyLawful`); the keys
  `succsL` asks about form such a family (`Config.SameProg`). -/

/-- Every leaf state of an event tree satisfies `P`. -/
def EvTree.All {σ : Type} (P : σ → Prop) : EvTree σ → Prop
  | .done s => P s
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).All P
  | .load _ _ _ ret => ∀ v, (ret v).All P
  | .store _ _ _ _ ret => ∀ b, (ret b).All P
  | .rmw _ _ _ _ ret => ∀ v, (ret v).All P
  | .fence _ ret => ∀ u, (ret u).All P

theorem EvTree.All.of_forall {σ : Type} {P : σ → Prop} (h : ∀ s, P s) : ∀ tree : EvTree σ, tree.All P
  | .done s => h s
  | .fault _ => trivial
  | .choose _ k => fun i => of_forall h (k i)
  | .load _ _ _ ret => fun v => of_forall h (ret v)
  | .store _ _ _ _ ret => fun b => of_forall h (ret b)
  | .rmw _ _ _ _ ret => fun v => of_forall h (ret v)
  | .fence _ ret => fun u => of_forall h (ret u)

theorem EvTree.All.map {σ τ : Type} {P : τ → Prop} (f : σ → τ) (h : ∀ s, P (f s)) :
    ∀ tree : EvTree σ, (tree.map f).All P
  | .done s => h s
  | .fault _ => trivial
  | .choose _ k => fun i => map f h (k i)
  | .load _ _ _ ret => fun v => map f h (ret v)
  | .store _ _ _ _ ret => fun b => map f h (ret b)
  | .rmw _ _ _ _ ret => fun v => map f h (ret v)
  | .fence _ ret => fun u => map f h (ret u)

/-- What `I.beqState` decides, for the certification cache: it is an
equivalence compatible with `hashState`, and on states with the same static
part (`static`: the state with its dynamic part erased, e.g. the program and
its layout) it is equality. An instruction does not change the static part.
Instances: AArch64, x64 (`static` erases the machine state), Toy (`beqState`
is equality outright). -/
class ISA.LawfulState (I : ISA) where
  /-- The static part of a state: what `beqState` need not compare. -/
  static : I.State → I.State
  beq_refl : ∀ a, I.beqState a a = true
  beq_symm : ∀ a b, I.beqState a b = true → I.beqState b a = true
  beq_trans : ∀ a b c, I.beqState a b = true → I.beqState b c = true → I.beqState a c = true
  hash_eq : ∀ a b, I.beqState a b = true → I.hashState a = I.hashState b
  eq_of_beq : ∀ a b, I.beqState a b = true → static a = static b → a = b
  exec_static : ∀ a tree, I.exec a = some tree → tree.All (fun s => static s = static a)

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- The state of a successful run of an event tree is one of its leaves. -/
theorem runTree_all {σ : Type} {P : σ → Prop} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → tree.All P → P s := by
  induction tree with
  | done s0 =>
    intro c s c' h hP
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hP
  | fault msg =>
    intro c s c' h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' h hP
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hi (hP i)
  | load k xcl l ret ih =>
    intro c s c' h hP
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, -, h⟩ := h
    exact ih v c0 s c' h (hP v)
  | store k xcl l v ret ih =>
    intro c s c' h hP
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, -, h⟩ := h
      exact ih true c0 s c' h (hP true)
    · rw [List.mem_ite_nil_right] at h
      exact ih false _ s c' h.2 (hP false)
  | fence k ret ih =>
    intro c s c' h hP
    simp only [runTree] at h
    exact ih () _ s c' h (hP ())
  | rmw k noRet l op ret ih =>
    intro c s c' h hP
    simp only [runTree] at h
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, -, h⟩ := h
    simp only at h
    split at h
    · exact ih old _ s c' h (hP old)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, -, h⟩ := h
      exact ih old _ s c' h (hP old)

end Rules

private theorem foldl_st {α : Type} (f : Thread I → α → Thread I) (hf : ∀ t a, (f t a).st = t.st) :
    ∀ (l : List α) (t : Thread I), (l.foldl f t).st = t.st
  | [], _ => rfl
  | a :: l, t => (foldl_st f hf l (f t a)).trans (hf t a)

/-- Close `(l₁.foldl f₁ (… (lₙ.foldl fₙ t))).st = s` where each `fᵢ` only
sets register views. -/
local macro "st_foldl" : tactic =>
  `(tactic| (repeat (refine (foldl_st _ ?_ _ _).trans ?_; (intro t a; first | rfl | (cases a; rfl)))
             try rfl))

/-- `finishInstr` sets the ISA state and touches only views otherwise. -/
theorem finishInstr_st {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {th : Thread I} (h : th ∈ finishInstr t d iv st c) : th.st = st := by
  unfold finishInstr at h
  simp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> split <;> (try split) <;> st_foldl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    split <;> split <;> st_foldl

/-- The state of every outcome of an instruction is a leaf of the
instruction's event tree. -/
theorem stepOne_leaf (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {P : I.State → Prop} (hP : ∀ tree, I.exec t.st = some tree → tree.All P) :
    P o.thread.st := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      rw [finishInstr_st hth]
      exact runTree_all A tid _ tree _ st c' hr (hP tree hex)

theorem stepOne_static (A : Arch) [L : I.LawfulState] {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : L.static o.thread.st = L.static t.st :=
  stepOne_leaf A hstep ho (L.exec_static t.st)

theorem ThreadNP.tail {A : Arch} {tid : Nat} {p q r : Thread I × Memory} (h : ThreadNP A tid p q)
    (hs : ThreadStep A tid q r) : ThreadNP A tid p r := by
  induction h with
  | refl => exact .step hs (.refl _)
  | step h₁ _ ih => exact .step h₁ (ih hs)

/-- An entry of `certify.go`'s search from `(t0, mem0)`: its state is reached
by a promise-free run, and the writes it carries are performed on such runs. -/
def GoEntry (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory)
    (e : Thread I × Memory × List (Msg × View) × Bool) : Prop :=
  ThreadNP A tid (t0, mem0) (e.1, e.2.1) ∧ ∀ p ∈ e.2.2.1, CertWrite A tid t0 mem0 p

/-- **The search is sound**: from sound entries, `certify.go` only adds
writes of promise-free runs, and claims `certified` only for a run that
empties the promise set. -/
theorem certify_go_sound (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory) :
    ∀ (n : Nat) (s : Std.HashSet (Thread I × Memory) × CertResult I) (e : Thread I × Memory × List (Msg × View) × Bool),
      GoEntry A tid t0 mem0 e → s.2.Sound A tid t0 mem0 → (certify.go A tid n s e).2.Sound A tid t0 mem0 := by
  -- the certification check: `acc` with the entry's writes, if it certifies
  have hchk : ∀ (acc : CertResult I) (t : Thread I) (mem : Memory) (ws : List (Msg × View)) (done : Bool),
      GoEntry A tid t0 mem0 (t, mem, ws, done) → acc.Sound A tid t0 mem0 → (!done && t.prom.isEmpty) = true →
      CertResult.Sound A tid t0 mem0 { acc with certified := true, writes := acc.writes ++ ws } := by
    intro acc t mem ws done he hs hc
    refine ⟨fun p hp => ?_, fun _ => ⟨t, mem, he.1, ?_⟩⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hs.1 p hp
      · exact he.2 p hp
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_iff] at hc
      exact hc.2
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
    by_cases hc : (!done && t.prom.isEmpty) = true
    · rw [ite_eq_left hc]
      have hs1 := hchk acc t mem ws done he hs hc
      dsimp only
      split
      · exact hs1
      · exact hs1
    · rw [ite_eq_right hc]
      dsimp only
      split
      · exact hs
      · exact hs
  | succ n ih =>
    rintro ⟨visited, acc⟩ ⟨t, mem, ws, done⟩ he hs
    rw [certify.go]
    split
    · exact hs
    dsimp only
    split
    · exact hs
    by_cases hc : (!done && t.prom.isEmpty) = true
    · rw [ite_eq_left hc]
      have hs1 := hchk acc t mem ws done he hs hc
      dsimp only
      split
      · exact hs1
      split
      · exact hs1
      rename_i outs hstep
      refine fold_then (P := fun R : List (Thread I × Memory × List (Msg × View) × Bool) × CertResult I =>
          (∀ e ∈ R.1, GoEntry A tid t0 mem0 e) ∧ R.2.Sound A tid t0 mem0)
        (Q := fun R => CertResult.Sound A tid t0 mem0 (List.foldl (certify.go A tid n) (visited.insert (t, mem), R.2) R.1).2)
        _ outs _ ⟨fun _ h => by simp at h, hs1⟩ ?_ ?_
      · rintro ⟨next, acc⟩ o ho ⟨hn, ha⟩
        cases o with
        | error m => exact ⟨hn, ha⟩
        | ok o =>
          have hnp : ThreadNP A tid (t0, mem0) (o.thread, o.mem) := he.1.tail ⟨outs, o, hstep, ho, rfl⟩
          have hw : ∀ p ∈ o.promisedNow, CertWrite A tid t0 mem0 p := fun p hp => ⟨t, mem, outs, o, he.1, hstep, ho, hp⟩
          dsimp only
          split
          · refine ⟨fun e he' => ?_, fun p hp => ?_, ha.2⟩
            · rcases List.mem_cons.mp he' with rfl | he'
              · exact ⟨hnp, fun _ h => by simp at h⟩
              · exact hn e he'
            · rcases List.mem_append.mp hp with hp | hp
              · exact ha.1 p hp
              · exact hw p hp
          · refine ⟨fun e he' => ?_, ha⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · refine ⟨hnp, fun p hp => ?_⟩
              rcases List.mem_append.mp hp with hp | hp
              · exact he.2 p hp
              · exact hw p hp
            · exact hn e he'
      · rintro ⟨next, acc⟩ ⟨hn, ha⟩
        exact foldl_inv (fun s : Std.HashSet (Thread I × Memory) × CertResult I => s.2.Sound A tid t0 mem0)
          (certify.go A tid n) next _ ha (fun s e he' hs' => ih s e (hn e he') hs')
    · rw [ite_eq_right hc]
      dsimp only
      split
      · exact hs
      split
      · exact hs
      rename_i outs hstep
      refine fold_then (P := fun R : List (Thread I × Memory × List (Msg × View) × Bool) × CertResult I =>
          (∀ e ∈ R.1, GoEntry A tid t0 mem0 e) ∧ R.2.Sound A tid t0 mem0)
        (Q := fun R => CertResult.Sound A tid t0 mem0 (List.foldl (certify.go A tid n) (visited.insert (t, mem), R.2) R.1).2)
        _ outs _ ⟨fun _ h => by simp at h, hs⟩ ?_ ?_
      · rintro ⟨next, acc⟩ o ho ⟨hn, ha⟩
        cases o with
        | error m => exact ⟨hn, ha⟩
        | ok o =>
          have hnp : ThreadNP A tid (t0, mem0) (o.thread, o.mem) := he.1.tail ⟨outs, o, hstep, ho, rfl⟩
          have hw : ∀ p ∈ o.promisedNow, CertWrite A tid t0 mem0 p := fun p hp => ⟨t, mem, outs, o, he.1, hstep, ho, hp⟩
          dsimp only
          split
          · refine ⟨fun e he' => ?_, fun p hp => ?_, ha.2⟩
            · rcases List.mem_cons.mp he' with rfl | he'
              · exact ⟨hnp, fun _ h => by simp at h⟩
              · exact hn e he'
            · rcases List.mem_append.mp hp with hp | hp
              · exact ha.1 p hp
              · exact hw p hp
          · refine ⟨fun e he' => ?_, ha⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · refine ⟨hnp, fun p hp => ?_⟩
              rcases List.mem_append.mp hp with hp | hp
              · exact he.2 p hp
              · exact hw p hp
            · exact hn e he'
      · rintro ⟨next, acc⟩ ⟨hn, ha⟩
        exact foldl_inv (fun s : Std.HashSet (Thread I × Memory) × CertResult I => s.2.Sound A tid t0 mem0)
          (certify.go A tid n) next _ ha (fun s e he' hs' => ih s e (hn e he') hs')

/-! ### The memo table -/

deriving instance ReflBEq, LawfulBEq for FwdItem
deriving instance ReflBEq, LawfulBEq for Views
deriving instance ReflBEq, LawfulBEq for Memory

theorem Thread.beq_iff (a b : Thread I) : (a == b) = true ↔
    I.beqState a.st b.st = true ∧ a.rview = b.rview ∧ a.wview = b.wview ∧ a.views = b.views ∧ a.prom = b.prom := by
  show Thread.beq a b = true ↔ _
  simp only [Thread.beq, Bool.and_eq_true, beq_iff_eq, and_assoc]

private theorem prod_beq_iff {α β : Type} [BEq α] [BEq β] (a b : α × β) :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show (a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true]

private instance instEquivBEqProd' {α β : Type} [BEq α] [BEq β] [EquivBEq α] [EquivBEq β] : EquivBEq (α × β) where
  rfl := (prod_beq_iff _ _).mpr ⟨BEq.rfl, BEq.rfl⟩
  symm h := (prod_beq_iff _ _).mpr ⟨BEq.symm ((prod_beq_iff _ _).mp h).1, BEq.symm ((prod_beq_iff _ _).mp h).2⟩
  trans h h' := (prod_beq_iff _ _).mpr ⟨BEq.trans ((prod_beq_iff _ _).mp h).1 ((prod_beq_iff _ _).mp h').1,
    BEq.trans ((prod_beq_iff _ _).mp h).2 ((prod_beq_iff _ _).mp h').2⟩

private instance instLawfulHashableProd' {α β : Type} [BEq α] [BEq β] [Hashable α] [Hashable β]
    [LawfulHashable α] [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq {a b} h := by
    obtain ⟨h1, h2⟩ := (prod_beq_iff a b).mp h
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    show mixHash (hash a1) (hash a2) = mixHash (hash b1) (hash b2)
    rw [show hash a1 = hash b1 from hash_eq h1, show hash a2 = hash b2 from hash_eq h2]

section Lawful

variable [L : I.LawfulState]

instance : EquivBEq (Thread I) where
  rfl {a} := (Thread.beq_iff a a).mpr ⟨L.beq_refl _, rfl, rfl, rfl, rfl⟩
  symm {a b} h := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff a b).mp h
    exact (Thread.beq_iff b a).mpr ⟨L.beq_symm _ _ h1, h2.symm, h3.symm, h4.symm, h5.symm⟩
  trans {a b c} h h' := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff a b).mp h
    obtain ⟨h1', h2', h3', h4', h5'⟩ := (Thread.beq_iff b c).mp h'
    exact (Thread.beq_iff a c).mpr ⟨L.beq_trans _ _ _ h1 h1', h2.trans h2', h3.trans h3', h4.trans h4', h5.trans h5'⟩

instance : LawfulHashable (Thread I) where
  hash_eq {a b} h := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff a b).mp h
    show Thread.hash a = Thread.hash b
    simp only [Thread.hash, L.hash_eq _ _ h1, h2, h3, h4, h5]

end Lawful

/-- The cache is sound on the keys whose thread and id satisfy `K`. -/
def CacheSoundOn (A : Arch) (K : Thread I → Nat → Prop) (cache : CertCache I) : Prop :=
  ∀ (t : Thread I) (tid : Nat) (mem : Memory) (r : CertResult I),
    K t tid → cache[(t, tid, mem)]? = some r → r.Sound A tid t mem

theorem CacheSound.on {A : Arch} {cache : CertCache I} (h : CacheSound A cache) (K : Thread I → Nat → Prop) :
    CacheSoundOn A K cache :=
  fun t tid mem r _ hr => h t tid mem r hr

/-- On the keys satisfying `K`, `==` is equality. -/
def KeyLawful (K : Thread I → Nat → Prop) : Prop :=
  ∀ (t t' : Thread I) (tid : Nat), K t tid → K t' tid → (t == t') = true → t = t'

theorem CacheSoundOn.insert [I.LawfulState] {A : Arch} {K : Thread I → Nat → Prop} {cache : CertCache I}
    (hK : KeyLawful K) (hc : CacheSoundOn A K cache) {t : Thread I} {tid : Nat} {mem : Memory} {r : CertResult I}
    (ht : K t tid) (hr : r.Sound A tid t mem) : CacheSoundOn A K (cache.insert (t, tid, mem) r) := by
  intro t' tid' mem' r' ht' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    obtain ⟨h1, h23⟩ := (prod_beq_iff _ _).mp heq
    obtain ⟨h2, h3⟩ := (prod_beq_iff _ _).mp h23
    simp only [beq_iff_eq] at h2 h3
    subst h2 h3
    cases h
    rw [← hK t t' tid ht ht' h1]
    exact hr
  · exact hc t' tid' mem' r' ht' h

/-- **`certify` is sound** (Kraken's Lemma 1 for the implementation): for a
query in a family of keys on which `==` is equality, and a cache sound on
that family, the result is sound and the cache stays sound on the family. -/
theorem certify_sound [I.LawfulState] {A : Arch} {K : Thread I → Nat → Prop} (hK : KeyLawful K)
    {cache : CertCache I} (hc : CacheSoundOn A K cache) {t : Thread I} {tid : Nat} (ht : K t tid)
    (mem : Memory) (fuel : Nat) :
    (certify A cache t tid mem fuel).1.Sound A tid t mem ∧ CacheSoundOn A K (certify A cache t tid mem fuel).2 := by
  unfold certify
  split
  · rename_i r h
    exact ⟨hc t tid mem r ht h, hc⟩
  · have hr := certify_go_sound A tid t mem fuel ({}, {}) (t, mem, [], false)
      ⟨.refl _, fun _ h => by simp at h⟩ ⟨fun _ h => by simp at h, fun h => by simp at h⟩
    exact ⟨hr, hc.insert hK ht hr⟩

/-- If `beqState` is equality outright, `==` on threads is equality. -/
theorem keyLawful_of_eq (h : ∀ a b, I.beqState a b = true → a = b) (K : Thread I → Nat → Prop) :
    KeyLawful K := by
  intro t t' _ _ _ hb
  obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff t t').mp hb
  have h1 := h _ _ h1
  cases t; cases t'
  simp_all

/-- `CertifySound`, for every cache, when `beqState` is equality outright
(the Toy ISA). -/
theorem certifySound [I.LawfulState] (A : Arch) (h : ∀ a b, I.beqState a b = true → a = b) :
    CertifySound A I := fun _ _ _ mem fuel hc =>
  let ⟨h1, h2⟩ := certify_sound (K := fun _ _ => True) (keyLawful_of_eq h _) (hc.on _) trivial mem fuel
  ⟨h1, fun t tid mem r hr => h2 t tid mem r trivial hr⟩

/-- The threads `succsL` asks `certify` about for thread id `tid` of `c`:
those with the static part of `c`'s thread `tid` (its successors by
`stepOne_static`). -/
def Config.SameProg [L : I.LawfulState] (c : Config I) (t : Thread I) (tid : Nat) : Prop :=
  ∃ t0, c.threads[tid]? = some t0 ∧ L.static t.st = L.static t0.st

theorem Config.SameProg.keyLawful [L : I.LawfulState] (c : Config I) : KeyLawful c.SameProg := by
  rintro t t' tid ⟨t0, h0, hs⟩ ⟨t0', h0', hs'⟩ hb
  rw [h0] at h0'
  cases h0'
  obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff t t').mp hb
  have h1 := L.eq_of_beq _ _ h1 (hs.trans hs'.symm)
  cases t; cases t'
  simp_all

/-! ## The machine successors -/

/-- What a `succs` successor of `c` is: an instruction step of some thread,
or a promise of a write that thread performs on a promise-free run from
`c` (appended at `|M| + 1`). -/
inductive SuccKind (A : Arch) (c : Config I) : Config I → Prop
  | instr {tid : Nat} {t : Thread I} {outs : List (Except String (Outcome I))} {o : Outcome I} :
      c.threads[tid]? = some t → stepOne A t tid c.mem = some outs → .ok o ∈ outs →
      SuccKind A c (c.withThread tid o.thread o.mem)
  | promise {tid : Nat} {t : Thread I} {p : Msg × View} :
      c.threads[tid]? = some t → CertWrite A tid t c.mem p →
      SuccKind A c (c.withThread tid { t with prom := t.prom ++ [(c.mem.append { p.1 with tid }).2] }
        (c.mem.append { p.1 with tid }).1)

theorem stepThread_eq_some {A : Arch} {c : Config I} {tid : Nat} {outs : List (Except String (Outcome I))}
    (h : stepThread A c tid = some outs) : ∃ t, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs := by
  unfold stepThread at h
  cases ht : c.threads[tid]? with
  | none => rw [ht] at h; cases h
  | some t => rw [ht] at h; exact ⟨t, rfl, h⟩

/-- The promises `certifiedPromises` offers are certified (`SuccKind`); the
cache stays sound on the keys `succsL` asks about (`Config.SameProg`). -/
theorem certifiedPromises_spec {A : Arch} [I.LawfulState] (cache : CertCache I) (c : Config I)
    (hc : CacheSoundOn A c.SameProg cache) (tid fuel : Nat) :
    CacheSoundOn A c.SameProg (certifiedPromises A cache c tid fuel).2.2 ∧
      ∀ y ∈ (certifiedPromises A cache c tid fuel).1, SuccKind A c y.1 := by
  unfold certifiedPromises
  split
  · exact ⟨hc, fun _ h => by cases h⟩
  · rename_i t ht
    obtain ⟨hw, hc'⟩ := certify_sound (Config.SameProg.keyLawful c) hc ⟨t, ht, rfl⟩ c.mem fuel
    refine ⟨hc', ?_⟩
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨w, hw', rfl⟩ := hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hw')
    exact SuccKind.promise ht (hw.1 p (List.mem_filter.mp hp).1)

/-- Every successor `succsL` collects is an instruction step or a certified
promise (`SuccKind`); the certification cache stays sound on the keys
`succsL` asks about. (`succsL` is a fold over threads, each a fold over
outcomes.) -/
theorem succsL_spec {A : Arch} [I.LawfulState] {fuel : Nat} {mp : Option Nat} (c : Config I)
    (cache : CertCache I) (hc : CacheSound A cache) : ∀ x ∈ (succsL A cache c fuel mp).1, SuccKind A c x.1 := by
  unfold succsL
  refine (foldl_inv (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
      CacheSoundOn A c.SameProg acc.2.2.2 ∧ ∀ x ∈ acc.1, SuccKind A c x.1) _ _ _
      ⟨hc.on _, fun _ h => by cases h⟩ ?_).2
  rintro ⟨next, bound, faults, cache⟩ tid - ⟨hc, hn⟩
  have key : ∀ (F : List (Config I × List TraceEv) × Bool × List String × CertCache I)
      (ps : List (Config I × TraceEv)), (CacheSoundOn A c.SameProg F.2.2.2 ∧ ∀ x ∈ F.1, SuccKind A c x.1) →
      (∀ y ∈ ps, y ∈ (certifiedPromises A F.2.2.2 c tid fuel).1) →
      CacheSoundOn A c.SameProg (certifiedPromises A F.2.2.2 c tid fuel).2.2 ∧
        ∀ x ∈ F.1.reverse ++ List.map (fun x => (x.1, [x.2])) ps, SuccKind A c x.1 := by
    intro F ps ⟨hF, hF1⟩ hps
    obtain ⟨hc', hp'⟩ := certifiedPromises_spec _ c hF tid fuel
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
    · exact mem_ite_nil hy
    · exact hy
  simp only
  split
  · exact key _ _ ⟨hc, hn⟩ (hsub _)
  · rename_i outs hstep
    obtain ⟨t, ht, hstep⟩ := stepThread_eq_some hstep
    refine key _ _ (foldl_inv (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
        CacheSoundOn A c.SameProg acc.2.2.2 ∧ ∀ x ∈ acc.1, SuccKind A c x.1) _ _ _ ⟨hc, hn⟩ ?_) (hsub _)
    rintro ⟨next, bound, faults, cache⟩ o ho ⟨hc, hn⟩
    cases o with
    | error m => exact ⟨hc, hn⟩
    | ok o =>
      have hnew : SuccKind A c (c.withThread tid o.thread o.mem) := .instr ht hstep ho
      obtain ⟨-, hc'⟩ := certify_sound (Config.SameProg.keyLawful c) hc
        ⟨t, ht, stepOne_static A hstep ho⟩ o.mem fuel
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

/-- **Every successor is an instruction step or a certified promise**, for
every ISA with `ISA.LawfulState`. -/
theorem succs_cases {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : c' ∈ (succs A c fuel).1) : SuccKind A c c' := by
  unfold succs at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact succsL_spec c {} (fun _ _ _ _ h => by simp at h) x hx

/-! ## Promise-free machine steps -/

/-- A machine step that is an instruction step of some thread (not a promise
step). The configuration may carry outstanding promises, of any thread; the
step may fulfil one. Unlike `ReachablePF` (`Conservative.lean`), nothing
requires the configurations to be promise-free: this is SLR's `−→NP` lifted
to the machine, which is what `npsafe` quantifies over. -/
def NPStep (A : Arch) (fuel : Nat) (c c' : Config I) : Prop :=
  c' ∈ (succs A c fuel).1 ∧ ∃ tid t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧
    .ok o ∈ outs ∧ c' = c.withThread tid o.thread o.mem

/-- Reachability along promise-free machine steps (outstanding promises
allowed, no new ones). -/
inductive NPReachable (A : Arch) (fuel : Nat) : Config I → Config I → Prop
  | refl (c : Config I) : NPReachable A fuel c c
  | step {c c' c'' : Config I} : NPStep A fuel c c' → NPReachable A fuel c' c'' → NPReachable A fuel c c''

theorem NPReachable.reachable {A : Arch} {fuel : Nat} {c c' : Config I} (h : NPReachable A fuel c c') :
    Reachable A fuel c c' := by
  induction h with
  | refl c => exact .refl c
  | step hs _ ih => exact .step hs.1 ih

/-! ## The write-invariant instance

Kang et al. §5.5 ("invariant-based program logic"), in SLR's architecture: a
per-location predicate `G` on values that every write preserves. The
hypothesis is about promise-free runs only (`ThreadNP`); the conclusion
covers every message of every `Reachable` configuration, promises included.
No hypothesis restricts the program: `G := fun _ _ => True` is always
dischargeable, and a racy program simply needs a weaker `G`. -/

/-- Every initial value and every message (fulfilled or promised) of `m`
satisfies `G`. Unsized and undeclared locations are covered through
`initVal`'s fallback `0`. -/
def MemInv (G : Loc → Val → Prop) (m : Memory) : Prop :=
  (∀ l, G l (m.initVal l)) ∧ ∀ w ∈ m.msgs.toList, G w.loc w.val

/-- Whatever a read returns satisfies `G`. -/
theorem MemInv.read? {G : Loc → Val → Prop} {m : Memory} (h : MemInv G m) {l : Loc} {t : Time} {v : Val}
    (hr : m.read? l t = some v) : G l v := by
  unfold Memory.read? at hr
  split at hr
  · cases hr; exact h.1 l
  · split at hr
    · rename_i w hw
      split at hr
      · rename_i hl
        cases hr
        have hl : w.loc = l := by simpa using hl
        subst hl
        unfold Memory.get? at hw
        rw [ite_eq_right (by assumption)] at hw
        exact h.2 w (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw))
      · cases hr
    · cases hr

theorem MemInv.of_ext {G : Loc → Val → Prop} {m m' : Memory} {ws : List Msg} (hi : m'.init = m.init)
    (hm : m'.msgs.toList = m.msgs.toList ++ ws) : MemInv G m' ↔ MemInv G m ∧ ∀ w ∈ ws, G w.loc w.val := by
  have hinit : ∀ l, m'.initVal l = m.initVal l := fun l => by simp only [Memory.initVal, hi]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨⟨fun l => hinit l ▸ h1 l, fun w hw => h2 w (by rw [hm]; exact List.mem_append_left _ hw)⟩,
      fun w hw => h2 w (by rw [hm]; exact List.mem_append_right _ hw)⟩
  · intro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun l => (hinit l).symm ▸ h1 l, fun w hw => ?_⟩
    rw [hm] at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact h2 w hw
    · exact h3 w hw

theorem MemInv.append {G : Loc → Val → Prop} {m : Memory} (h : MemInv G m) {w : Msg} (hw : G w.loc w.val) :
    MemInv G (m.append w).1 :=
  (MemInv.of_ext (m := m) (m' := (m.append w).1) (ws := [w]) rfl (by simp [Memory.append])).mpr ⟨h, by simpa using hw⟩

/-- **The write obligation.** From every configuration reachable from `c0`,
every instruction a thread performs on a promise-free run of its own, from a
memory satisfying `MemInv G`, yields a memory satisfying `MemInv G`.
Equivalently (`stepOne_ext`), each write it appends satisfies `G`. Runs of the
thread alone are included because certification runs are such runs. -/
def WritesPreserve (A : Arch) (fuel : Nat) (G : Loc → Val → Prop) (c0 : Config I) : Prop :=
  ∀ c, Reachable A fuel c0 c → ∀ tid t, c.threads[tid]? = some t →
    ∀ t1 mem1, ThreadNP A tid (t, c.mem) (t1, mem1) → MemInv G mem1 →
      ∀ outs o, stepOne A t1 tid mem1 = some outs → .ok o ∈ outs → MemInv G o.mem

/-- A promise-free run of one thread preserves `MemInv G` if each of its
steps does. -/
theorem ThreadNP.memInv {A : Arch} {tid : Nat} {G : Loc → Val → Prop} {p q : Thread I × Memory}
    (h : ThreadNP A tid p q)
    (hstep : ∀ t1 mem1, ThreadNP A tid p (t1, mem1) → MemInv G mem1 →
      ∀ outs o, stepOne A t1 tid mem1 = some outs → .ok o ∈ outs → MemInv G o.mem)
    (hp : MemInv G p.2) : MemInv G q.2 := by
  induction h with
  | refl => exact hp
  | @step p p' q hs _ ih =>
    obtain ⟨outs, o, h1, h2, rfl⟩ := hs
    refine ih (fun t1 mem1 hr => hstep t1 mem1 (.step ⟨outs, o, h1, h2, rfl⟩ hr)) ?_
    exact hstep p.1 p.2 (.refl _) hp outs o h1 h2

/-- The write invariant over promise-free machine runs: unconditional. -/
theorem write_invariant_np {A : Arch} {fuel : Nat} {G : Loc → Val → Prop} {c0 c : Config I}
    (h0 : MemInv G c0.mem) (H : WritesPreserve A fuel G c0) (h : NPReachable A fuel c0 c) : MemInv G c.mem := by
  suffices ∀ c c', NPReachable A fuel c c' → Reachable A fuel c0 c → MemInv G c.mem → MemInv G c'.mem from
    this c0 c h (.refl c0) h0
  intro c c' h
  induction h with
  | refl => exact fun _ hm => hm
  | @step c c' c'' hs _ ih =>
    intro hr hm
    obtain ⟨hmem, tid, t, outs, o, ht, hstep, ho, rfl⟩ := hs
    exact ih (Reachable.trans A fuel hr (Reachable.single A fuel hmem)) (H c hr tid t ht t c.mem (.refl _) hm outs o hstep ho)

/-- **The write invariant over the full machine, promises included**: every
message of every configuration reachable from `c0` satisfies `G`, given the
write obligation on promise-free runs. No other hypothesis: `ISA.LawfulState`
(what the certification cache's `beqState` decides) holds for AArch64, x64
and Toy. -/
theorem write_invariant {A : Arch} [I.LawfulState] {fuel : Nat} {G : Loc → Val → Prop} {c0 c : Config I}
    (h0 : MemInv G c0.mem) (H : WritesPreserve A fuel G c0)
    (h : Reachable A fuel c0 c) : MemInv G c.mem := by
  suffices ∀ c c', Reachable A fuel c c' → Reachable A fuel c0 c → MemInv G c.mem → MemInv G c'.mem from
    this c0 c h (.refl c0) h0
  intro c c' h
  induction h with
  | refl => exact fun _ hm => hm
  | @step c c' c'' hs _ ih =>
    intro hr hm
    refine ih (Reachable.trans A fuel hr (Reachable.single A fuel hs)) ?_
    cases succs_cases hs with
    | instr ht hstep ho => exact H c hr _ _ ht _ c.mem (.refl _) hm _ _ hstep ho
    | @promise tid t p ht hw =>
      obtain ⟨t1, mem1, outs, o, hnp, hstep, ho, hp⟩ := hw
      have hstepH := H c hr tid t ht
      have hm1 : MemInv G mem1 := hnp.memInv (fun t1 mem1 hr' => hstepH t1 mem1 hr') hm
      have hmo := hstepH t1 mem1 hnp hm1 outs o hstep ho
      obtain ⟨hi, hmsgs⟩ := stepOne_ext A hstep ho
      have hG := ((MemInv.of_ext hi hmsgs).mp hmo).2 p.1 (List.mem_map_of_mem hp)
      exact hm.append hG

/-! ## SLR's safety predicates over Kraken (Figs. 7–8), as `Prop`s

The resource model is a parameter (`ResModel`): SLR's resources and erasure
for the chosen assertion language. States are
whole configurations and a thread id; the local state of the thread is
`c.threads[tid]`. Simplifications against SLR, none of which matters for the
shape of Theorem 1: the frame `f` of weak erasure (`r • f`) and upward
closure in `(M, V, r)` are folded into `erase`; the world order `W' ≥ W` into
`Ghost`; view shifts at termination into `B`. -/

/-- A resource model for the n-thread logic. -/
structure ResModel (I : ISA) where
  /-- Per-thread resources (SLR's `Res`: write permissions with their write
  sets, acquire permissions). -/
  R : Type
  /-- Global ghost state: the resources attached to messages (`u`) and the
  world (`W`). -/
  Ghost : Type
  /-- Erasure `⌊rF, u, W⌋_T`: the configuration respects the threads'
  resources and the ghost state; outstanding promises of threads in `T` are
  not required to respect resources. -/
  erase : (Nat → R) → Ghost → (Nat → Prop) → Config I → Prop
  /-- `r.wr(l).perm > 0`: the thread owns a write permission for `l`. -/
  owns : R → Loc → Prop
  /-- `r' • canAcq(r', u') ≤o r • canAcq(r, u)`: no write permission becomes
  ownable or acquirable that was not before. -/
  acqLe : R → Ghost → R → Ghost → Prop
  /-- SLR's world order `W ≤ W'` on ghost states, with the message resources
  `u` (and whatever else erasure alone constrains) free: the facts a thread's
  assertions may rely on across other threads' steps (release predicates,
  acquire predicates by id). `NPSafe` is closed under it, as SLR's `npsafe`
  is closed under world extension and quantifies over `u` at every step
  (Theorem 1′ restatement). -/
  ghostLe : Ghost → Ghost → Prop
  /-- The outstanding promise `ts` is *pending* in the ghost state: it is
  erased as a written message (option (B): its release event was prepaid at
  promise time by `NPSafe`'s prepay conjunct, and the thread's fulfilling
  instruction is its next one in the virtual configuration, pending-release
  clause). Option (B) removed
  the original design's `markPending` (marking is done by the instance's lemmas,
  `SLR.erase_pending`, inside Theorem 1′'s proof). -/
  pendingAt : Ghost → Time → Prop
  /-- `reach r g x b`: the thread may write `x` using only its own resource
  and resources attached to messages at timestamps `≤ b` (for
  condition (3), the bounded-reach proposal): a bounded `mayWrite`. `NPSafe`'s step
  conclusion constrains how it changes (`K1`, `K2` there), which is what lets
  Theorem 1′ chain a later write permission back to an earlier configuration
  (condition (3), steps 2–4). -/
  reach : R → Ghost → Loc → Time → Prop

/-- `rF[tid ↦ r]`. -/
def ResModel.upd {I : ISA} (M : ResModel I) (rF : Nat → M.R) (tid : Nat) (r : M.R) : Nat → M.R :=
  fun i => if i = tid then r else rF i

/-- SLR's `wf_prom(P(i), V)`: every outstanding promise of the thread is
above its views, i.e. can still be fulfilled (`Thread.hasDeadPromise`). The
read rule's `prom` filter (`readSuccs`) is the other half: a thread never
reads its own outstanding promise. -/
def Config.WfProm (c : Config I) (tid : Nat) : Prop :=
  ∀ t, c.threads[tid]? = some t → t.hasDeadPromise c.mem = false

/-- The messages thread `tid` writes on a step from `c` to `c'` (SLR's
`(M' \ P') \ (M \ P)`): appended at a fresh timestamp and not left
outstanding, or an outstanding promise fulfilled. -/
def Written (tid : Nat) (c c' : Config I) (w : Msg) : Prop :=
  ∃ ts, c'.mem.get? ts = some w ∧
    (∀ t', c'.threads[tid]? = some t' → ts ∉ t'.prom) ∧
    (c.mem.last < ts ∨ ∀ t, c.threads[tid]? = some t → ts ∈ t.prom)

/-- An instruction step of thread `tid` alone (`−→NP`), without the
consistency check `succs` adds. -/
def NPStepBy (A : Arch) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ t t' mem', c.threads[tid]? = some t ∧ ThreadStep A tid (t, c.mem) (t', mem') ∧
    c' = c.withThread tid t' mem'

/-- A machine step of thread `tid`: an instruction step or a promise, each a
`succs` successor (so certified). -/
def StepBy (A : Arch) (fuel : Nat) (tid : Nat) (c c' : Config I) : Prop :=
  c' ∈ (succs A c fuel).1 ∧
    (NPStepBy A tid c c' ∨
      ∃ (t : Thread I) (w : Msg), c.threads[tid]? = some t ∧
        c' = c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] }
          (c.mem.append { w with tid }).1)

/-- `c₁` is `c` after steps of the environment: other threads' steps and
promises of thread `tid` itself. The memory has only grown, and `tid`'s state
is unchanged except that its promise set may have grown by new timestamps.
SLR builds this closure into its predicates (`∀ (M, V, r) ≥ (M₁, V₁, r₁)`,
the promise set being part of the global configuration); without it safety
would not survive interference, nor a promise step in Theorem 1's proof.
Growth of the resource (`r ≥ r₁`) is folded into `ResModel.erase`. -/
def EnvExt (tid : Nat) (c c₁ : Config I) : Prop :=
  c₁.mem.init = c.mem.init ∧ c.mem.msgs.toList <+: c₁.mem.msgs.toList ∧
    ∀ t, c.threads[tid]? = some t →
      ∃ ps : List Time, c₁.threads[tid]? = some { t with prom := t.prom ++ ps } ∧ ∀ p ∈ ps, c.mem.last < p

/-- **The machine invariants** of a configuration: every outstanding promise
is a message of its thread (`promWf`: the `hwf` of `Erase.unfulfil` and
`Erase.ofVirtualOf`, and `Erase.promWf`), promise sets are duplicate-free,
and every message of a thread that is not one of its outstanding promises is
at most the thread's coherence view of its location (`ownCoh`: the thread
form of `Ctx.OwnCoh`, the thread half of RMW uniqueness).

Defined here (it was in `SLR/Invariants.lean`, which proves it reachable:
`Config.MachInv.reachable`) because `NPSafe`'s step assumes it of the
environment extension `c₁`, which need not be reachable (Theorem 1′
restatement). -/
structure Config.MachInv (c : Config I) : Prop where
  promWf : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → ∀ p ∈ t.prom, ∃ w, c.mem.get? p = some w ∧ w.tid = i
  promNodup : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.prom.Nodup
  ownCoh : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t →
    ∀ ts w, c.mem.get? ts = some w → w.tid = i → ts ∉ t.prom → ts ≤ t.views.getCoh w.loc

/-- The context after an RMW's write (`runTree`): `rmwWrote`, and for an
acquire-release (not `noRet`) RMW, everything after it ordered after its
write. -/
def rmwPost (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) : Ctx :=
  let c := { c with rmwWrote := true }
  if A.rmwKind k == .acqRel && !noRet then
    let t := c.views.getCoh l
    { c with views := { c.views with vrNew := max c.views.vrNew t, vwNew := max c.views.vwNew t } }
  else c

/-- Some run of the event tree from `c` reaches a release store (after
`A.storeKind`) that fulfils the outstanding promise `ts`. Over-approximates
`runTree`'s runs (it ignores the store-exclusive pairing check), which only
makes `relPre_lt` stronger. -/
def EvTree.RelFulfils (A : Arch) (tid : Nat) (iv : InstrViews) (ts : Time) {σ : Type} :
    Ctx → EvTree σ → Prop
  | _, .done _ => False
  | _, .fault _ => False
  | c, .choose _ k => ∃ i, RelFulfils A tid iv ts c (k i)
  | c, .load k xcl l ret => ∃ x ∈ readSuccs A iv c k xcl l, RelFulfils A tid iv ts x.2.2 (ret x.2.1)
  | c, .store k xcl l v ret =>
    (∃ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0),
      (A.storeKind k = .rel ∧ ts ∈ c.prom ∧ ts ∉ c'.prom) ∨ RelFulfils A tid iv ts c' (ret true)) ∨
    RelFulfils A tid iv ts
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } (ret false)
  | c, .fence k ret => RelFulfils A tid iv ts (fenceStep c k) (ret ())
  | c, .rmw k noRet l op ret =>
    ∃ x ∈ readSuccs A iv (if A.rmwFence then fenceStep c .sy else c)
        (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      RelFulfils A tid iv ts (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2) (ret x.2.1) ∨
      ∃ new, op x.2.1 = some new ∧
        ∃ c' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
          (A.storeKind (A.rmwKind k).storeKind = .rel ∧ ts ∈ x.2.2.prom ∧ ts ∉ c'.prom) ∨
          RelFulfils A tid iv ts
            (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c') (ret x.2.1)

/-- The next instruction of thread `t`, run against `mem`, can fulfil the
outstanding promise `ts` with a release store. -/
def Thread.RelFulfils (A : Arch) (tid : Nat) (ts : Time) (t : Thread I) (mem : Memory) : Prop :=
  ∃ tree, I.exec t.st = some tree ∧
    EvTree.RelFulfils A tid (instrViews t (I.deps t.st)) ts
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree

/-- No outstanding promise of the context is dead: each lies above the
context's `coh` of its location, `vwNew` and `vCAP` (the `Ctx` form of
`Thread.hasDeadPromise = false`). -/
def Ctx.NoDead (c : Ctx) : Prop :=
  ∀ p ∈ c.prom, ∀ w, c.mem.get? p = some w → max (c.views.getCoh w.loc) (max c.views.vwNew c.views.vCAP) < p

/-- `EvTree.RelFulfils` through a run that leaves no outstanding promise dead
right after the fulfilling write (`Ctx.NoDead`). This is the form `NPSafe`'s
prepay conjunct asks for (T1c (4)): a release that kills another promise of
the thread (for instance by fulfilling a later one at the same location)
cannot occur on a path to a final configuration, so it need not be prepaid. -/
def EvTree.RelFulfilsLive (A : Arch) (tid : Nat) (iv : InstrViews) (ts : Time) {σ : Type} :
    Ctx → EvTree σ → Prop
  | _, .done _ => False
  | _, .fault _ => False
  | c, .choose _ k => ∃ i, RelFulfilsLive A tid iv ts c (k i)
  | c, .load k xcl l ret => ∃ x ∈ readSuccs A iv c k xcl l, RelFulfilsLive A tid iv ts x.2.2 (ret x.2.1)
  | c, .store k xcl l v ret =>
    (∃ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0),
      ((A.storeKind k = .rel ∧ ts ∈ c.prom ∧ ts ∉ c'.prom) ∧ c'.NoDead) ∨
        RelFulfilsLive A tid iv ts c' (ret true)) ∨
    RelFulfilsLive A tid iv ts
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } (ret false)
  | c, .fence k ret => RelFulfilsLive A tid iv ts (fenceStep c k) (ret ())
  | c, .rmw k noRet l op ret =>
    ∃ x ∈ readSuccs A iv (if A.rmwFence then fenceStep c .sy else c)
        (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      RelFulfilsLive A tid iv ts (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2) (ret x.2.1) ∨
      ∃ new, op x.2.1 = some new ∧
        ∃ c' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
          ((A.storeKind (A.rmwKind k).storeKind = .rel ∧ ts ∈ x.2.2.prom ∧ ts ∉ c'.prom) ∧ c'.NoDead) ∨
          RelFulfilsLive A tid iv ts
            (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c') (ret x.2.1)

/-- The next instruction of thread `t`, run against `mem`, can fulfil the
outstanding promise `ts` with a release store, leaving no promise dead
(`EvTree.RelFulfilsLive`). -/
def Thread.RelFulfilsLive (A : Arch) (tid : Nat) (ts : Time) (t : Thread I) (mem : Memory) : Prop :=
  ∃ tree, I.exec t.st = some tree ∧
    EvTree.RelFulfilsLive A tid (instrViews t (I.deps t.st)) ts
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree

theorem EvTree.RelFulfilsLive.toRelFulfils {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (c : Ctx), tree.RelFulfilsLive A tid iv ts c → tree.RelFulfils A tid iv ts c
  | .done _, _, h => h
  | .fault _, _, h => h
  | .choose _ k, c, ⟨i, h⟩ => ⟨i, toRelFulfils (k i) c h⟩
  | .load _ _ _ ret, _, ⟨x, hx, h⟩ => ⟨x, hx, toRelFulfils (ret x.2.1) _ h⟩
  | .store _ _ _ _ ret, _, h => by
    rcases h with ⟨c', hc', ⟨h, -⟩ | h⟩ | h
    · exact .inl ⟨c', hc', .inl h⟩
    · exact .inl ⟨c', hc', .inr (toRelFulfils (ret true) _ h)⟩
    · exact .inr (toRelFulfils (ret false) _ h)
  | .fence _ ret, _, h => toRelFulfils (ret ()) _ h
  | .rmw _ _ _ _ ret, _, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', ⟨h, -⟩ | h⟩
    · exact ⟨x, hx, .inl (toRelFulfils (ret x.2.1) _ h)⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inl h⟩⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inr (toRelFulfils (ret x.2.1) _ h)⟩⟩

theorem Thread.RelFulfilsLive.toRelFulfils {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : t.RelFulfilsLive A tid ts mem) : t.RelFulfils A tid ts mem := by
  obtain ⟨tree, hex, h⟩ := h
  exact ⟨tree, hex, EvTree.RelFulfilsLive.toRelFulfils tree _ h⟩

section Safety

variable (M : ResModel I) (A : Arch) (fuel : Nat) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat)

/-- Thread `tid` has halted with no outstanding promise. -/
def Config.Done (c : Config I) (tid : Nat) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ t.halted = true ∧ t.prom = []

/-- **SLR Fig. 8, non-promising safety**, indexed by `(n, m)` ordered
lexicographically: thread `tid`'s instruction steps (no promise steps; the
configuration may carry promises) respect resources. Each step may only lose
ownable-or-acquirable write permissions (`acqLe`), and every message it
writes or fulfils needs a write permission it owns.

Shape of the Theorem 1′ restatement; the
differences from SLR's `npsafe` and from the shape:

- **ghost quantified per step** (`g₁` with `M.ghostLe g g₁`, the conclusion
  `M.ghostLe g₁ g'`): other threads' steps change the message resources, so
  a predicate that fixed the ghost state could not be applied after them.
  SLR quantifies over `u` at every step and closes `npsafe` under world
  extension; this is the same.
- **validity-free erasure** (`fun _ => True`: no thread's outstanding
  promises need be valid, before or after). SLR uses weak erasure
  `⌊…⌋_{tid}`, which asks the step to keep *other* threads' promises valid;
  with RMW claims that is not a local fact (`hval` of `Erase.rmw`/
  `Erase.store`, R3). Here validity is Theorem 1′'s business: its
  path-relative condition (3) restores it from liveness (every promise of a
  live configuration is fulfilled later on the path, with a permission its
  thread owns then). With `T = fun _ => True`
  `Erase.npStep`'s `hval` obligations are vacuous.
- **machine invariants of `c₁`** (`c₁.MachInv`), next to `WfProm`: `c₁` is
  an arbitrary environment extension; Theorem 1′ discharges it with
  `Config.MachInv.reachable`/`.threadNP`.
- **own pending promises are the thread's own prepayments** (option (B)): the
  step assumes that every pending promise of `tid` at `g₁` was already pending
  at `g`, i.e. was created by `tid`'s own prepay conjunct (the environment
  never marks `tid`'s promises pending). For a thread with no prepayment this
  is the original design's "no own pending promise" (the `hnp` of the RMW rule); with
  one, the rule knows which promises are pending and to which locations
  (S2d's `ErAt.rmw_loc` needs only "no pending promise of `tid` to the RMW's
  location"). The step keeps every pending mark of a promise still
  outstanding after it (the real fulfilling instruction `F` of a prepaid
  release fulfils it as an ordinary step, `ErAt.fulfilPend`, which unpends
  it).
- **the prepay conjunct** (option (B), fallback (iii) for every promised
  release): for a promise of `tid` itself, at `c₁`, whose fulfilling
  instruction is `tid`'s next one (`Thread.RelFulfils`, with the promise
  added), a ghost step accounts the release event of that instruction at
  promise time: erasure of the promised configuration with the promise
  pending (`Erase.prepay` in the SLR instance), the
  thread's resource after the release event, and `NPSafe` of the result
  (which must then run the real instruction as an ordinary step, its other
  events on the real memory). Only the rule for that instruction can justify
  the prepayment (it splits the thread's resource), so it is a conjunct of
  `NPSafe`, not a law of the model. Theorem 1′ uses it at a release promise
  after replaying the thread's memory-silent advance ((S1′)). The release
  must leave the thread with no dead promise (`Thread.RelFulfilsLive`,
  T1c (4)): on a path to a final configuration every release fulfilment does,
  and a release that kills another promise (fulfilling a later one of two
  promises) needs no prepayment, which is what makes a second prepayment for
  the same instruction unnecessary.
- **pending marks exact**: a step creates no pending mark and
  keeps those of promises still outstanding; a prepayment adds exactly its
  own promise. Only prepayments mark promises pending, which is what makes
  the own-pending hypothesis dischargeable in Theorem 1′.
- **bounded reach, `K1`/`K2`** (for condition (3)):
  for every bound `b ≤ |M|` at `c₁`, the ghost change of a step (or a
  prepayment) adds nothing reachable from messages `≤ b` (`K2`, any
  resource `ρ`), and if the thread's views after the step stay `≤ b`
  (`vwNew`, `vCAP`: it acquired nothing above `b`) its own reach below `b`
  did not grow (`K1`). In the SLR instance: fresh slots sit above `|M|`,
  claims and acquisitions only remove slots, an acquire read above `b`
  raises `vwNew` above `b`.
- **the clean flag `cl`**: only
  the *functional* part is guarded by validity. The Done conjunct asks for `B`
  only while `cl` holds, and a step's (or a prepayment's) continuation keeps
  the flag only if full erasure (`fun _ => False`: every outstanding promise
  valid) held at the pre-state `c₁`; otherwise it drops to `False`. Every
  resource obligation (erasure `⊤`, `ghostLe`, marks, `acqLe`, `owns`,
  `K1`/`K2`, the prepay conjunct, the continuation itself) is unconditional,
  so Theorem 1′ builds its annotated run without validity and only afterwards
  uses condition (3) (validity at every annotated configuration) to show that
  every flag stayed `True`. A rule may thus use validity at its pre-state (e.g.
  a read under a lock returns no other thread's invalid promise) for its
  functional conclusion, but must still supply resources when validity fails.
  Proofs that never use validity hold for every `cl` (`NPSafe.mono_flag`). -/
def NPSafe : Nat → Nat → Prop → Config I → M.R → M.Ghost → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, 0, cl, c, r, g => ∀ m, NPSafe n m cl c r g
  | n + 1, m + 1, cl, c, r, g =>
    ∀ c₁ g₁, EnvExt tid c c₁ → M.ghostLe g g₁ →
    (cl → c₁.Done tid → B c₁ r g₁) ∧
    (∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → NPStepBy A tid c₁ c' →
      c₁.MachInv → c₁.WfProm tid → c'.WfProm tid →
      (∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
        (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
        NPSafe (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧ M.acqLe r' g' r g₁ ∧
        (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
        (∀ b, b ≤ c₁.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b) ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b)) ∧
    (∀ (rF : Nat → M.R) (t₁ : Thread I) (w : Msg), c₁.threads[tid]? = some t₁ →
      M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → c₁.MachInv →
      (∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }.RelFulfilsLive A tid
        (c₁.mem.append { w with tid }).2 (c₁.mem.append { w with tid }).1 →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafe (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        (∀ b, b ≤ c₁.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b) ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b))
termination_by n m => (n, m)

/-- **SLR Fig. 7, safety**: every machine step of thread `tid`, promise steps
included, re-establishes (full) erasure for some resources, and the thread
stays safe. As `NPSafe`, closed under ghost extension by the environment
(`g₁`, `M.ghostLe`). Superseded by Theorem 1′ (`NPSafeImpliesAdequateV`);
kept for reference. -/
def Safe : Nat → Config I → M.R → M.Ghost → Prop
  | 0, _, _, _ => True
  | n + 1, c, r, g =>
    ∀ c₁ g₁, EnvExt tid c c₁ → M.ghostLe g g₁ →
    (c₁.Done tid → B c₁ r g₁) ∧
    ∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁ → StepBy A fuel tid c₁ c' →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => False) c' ∧ M.ghostLe g₁ g' ∧ Safe n c' r' g'

end Safety

/-- The laws of a resource model that SLR's proof of Theorem 1 uses, in
Kraken's terms. `promise` is SLR's Lemmas 23–24 (a promise the thread may
write keeps erasure) restricted to messages that transfer no ownership
(`transfersNothing`, SLR's "relaxed messages satisfy their predicate with the
empty resource"); SLR discharges the remaining case, promised release writes,
by "release promises cannot be fulfilled", which is false in Kraken. That
case is `promisedRelease`, left open. -/
structure ResModel.Laws (M : ResModel I) where
  /-- Exempting more threads weakens erasure (SLR's promise weakening). -/
  weaken : ∀ rF g (T T' : Nat → Prop) (c : Config I), (∀ i, T i → T' i) → M.erase rF g T c → M.erase rF g T' c
  /-- The thread can write `l`: it owns or can acquire a write permission. -/
  mayWrite : M.R → M.Ghost → Loc → Prop
  /-- The message carries no ownership (its location's release predicate is
  pure at its value). -/
  transfersNothing : M.Ghost → Msg → Prop
  /-- SLR Lemmas 23–24, for any exemption set `T` (generalised from
  `T = ∅`; the promising thread must be able to write the location unless its
  promises are exempt). Theorem 1′ carries validity-free erasure
  (`T = fun _ => True`, see `NPSafe`), where only purity remains. -/
  promise : ∀ rF g (T : Nat → Prop) (c : Config I) tid t (w : Msg), M.erase rF g T c → c.threads[tid]? = some t →
    (¬ T tid → mayWrite (rF tid) g w.loc) → transfersNothing g w →
    M.erase rF g T
      (c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1)
  /-- SLR Lemma 21's conclusion from `owns` along a run and `acqLe`: what a
  thread owns is something it may write. -/
  owns_mayWrite : ∀ r g l, M.owns r l → mayWrite r g l
  /-- What a thread owns it can reach under any bound. -/
  owns_reach : ∀ r g l b, M.owns r l → M.reach r g l b
  /-- Bounded reach is a way of writing. -/
  reach_mayWrite : ∀ r g l b, M.reach r g l b → mayWrite r g l
  /-- Transitivity of `acqLe` with `mayWrite` (SLR Lemma 16). -/
  acqLe_mayWrite : ∀ r g r' g' l, M.acqLe r' g' r g → mayWrite r' g' l → mayWrite r g l
  /-- The world order is reflexive. -/
  ghostLe_refl : ∀ g, M.ghostLe g g
  /-- The world order is transitive. -/
  ghostLe_trans : ∀ g₁ g₂ g₃, M.ghostLe g₁ g₂ → M.ghostLe g₂ g₃ → M.ghostLe g₁ g₃

/-- **Theorem 1 for Kraken** (`npsafe(n+1, 0) ⊆ safe_n`), as a `Prop`: for a
resource model with its laws (and `ISA.LawfulState`, which makes
`succs_cases` available), non-promising safety of a
thread implies its safety over the full machine. Not proved (out of the
prototype's scope). Its proof follows SLR's Lemma 25: a promise step's message is
written by a promise-free run from the pre-promise configuration
(`succs_cases`: by definition in Kraken), so Lemma 21 gives `mayWrite`, and
`Laws.promise` re-establishes erasure if the message transfers nothing; an
instruction step's consistency (`CertOk`, from `certified`) gives the
promise-free run SLR uses to validate the thread's remaining promises.

**Superseded** by Theorem 1′ (`NPSafeImpliesAdequateV`): with promised
releases (R2) and RMW claims (R3) this step-indexed form is not expected to
hold (`Safe` demands full erasure after every step, `NPSafe` 
only validity-free erasure). Kept for reference. -/
def NPSafeImpliesSafe (M : ResModel I) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (_ : M.Laws) (B : Config I → M.R → M.Ghost → Prop) (tid n : Nat) (c : Config I)
    (r : M.R) (g : M.Ghost), NPSafe M A B tid (n + 1) 0 True c r g → Safe M A fuel B tid n c r g

/-! ## R2: promised release stores

SLR discharges the promise of a release write with "release write promises
cannot be fulfilled" (appendix, proof of Lemma 25, case `m.mod = rel`).
Kraken promises release stores. In the step-indexed `Safe` above, a promise
step keeps the thread's resource (`r' = r` in SLR's proof, the only resource
for which `NPSafe` is known), so a promised release could carry resources
only by duplicating them. Yet the explorer shows that another thread can
acquire through an outstanding promised release and use what it transfers
before the release is fulfilled, sometimes before the releasing thread has
even taken the lock. So the transfer must happen at promise time.

The design chosen, (V) *virtual advancement*, accounts a promised release in
a **virtual configuration** where the promising thread has already run,
alone and without changing memory, up to the instruction that fulfils the
release (variant (ii); "up to and including the fulfilment" is impossible in
general: that instruction may also append, e.g. x64 `movups`, see
`Config.AdvanceableStrict`). There the release is *pending at the thread's
next instruction*, and the thread holds, under `NPSafe`, exactly the
resources SLR's release rule would attach to it; erasure must count them
for the pending message (the erasure clause for
pending releases is a resource-model obligation, still to be fixed with the
`ResModel` instance; fallback (iii) is to run the whole instruction in a
virtual memory). No law lets an *outstanding, non-pending* release carry
resources. What (V) needs is:

- two machine facts about every program, Stage 2 lemmas, proved in
  `Kraken/Promising/ReleasePrefix.lean` and checked by the explorer
  (`PromiseSafeTests`, `ReleasePrefixTests`):
  (S1′) an outstanding promise that a release store fulfils on some path can
  be brought by a memory-silent promise-free run of its thread alone to the
  instruction that fulfils it (`Config.Advanceable`,
  `Config.advanceable_of_path`; the strict form, fulfilling it without
  changing memory, `Config.AdvanceableStrict`, fails at instruction
  granularity); (S2) every reachable instruction step of that thread before
  the fulfilment is a `StutterStep` (it appends nothing and reads nothing
  above the promise; `stutterStep_release`). Both follow from the release
  pre-view (`writeSuccs`: a release write lies above every earlier read and
  write of its thread), with no use of certification. The store kind of a
  fulfilment, which `Outcome` does not record, is read off the instruction's
  event tree (`EvTree.RelFulfils`);
- structural laws of the resource model (`ResModel.PromisedRelease`; option (B): `validate` only; the original design's pending laws
  `pending`/`fulfil` are lemmas of the SLR instance) and `NPSafe`'s prepay
  conjunct (the release event accounted at promise time, fallback (iii) for
  every promised release);
- Theorem 1 in a different shape (`NPSafeImpliesAdequateV`): its conclusions
  hold of a virtual configuration (`Config.VirtualOf`, or any `VirtualRel`),
  which is the real one in final configurations
  (`Config.VirtualOf.eq_of_final`).
-/

/-- (S1), strict form: the outstanding promise `ts` of thread `tid` can be
fulfilled by a promise-free run of thread `tid` alone that leaves memory
unchanged. **False in general**: an instruction that
performs two writes, the first a release fulfilling `ts` and the second a
fresh write (x64 `movups` to memory: two 8-byte TSO stores), cannot fulfil
`ts` without appending. The explorer counterexample is in
`PromiseSafeTests` (`advanceableStrict_movups`). This is instruction
granularity, not a program restriction; (V) uses `Config.Advanceable`. -/
def Config.AdvanceableStrict (A : Arch) (c : Config I) (tid : Nat) (ts : Time) : Prop :=
  ∃ t t', c.threads[tid]? = some t ∧ ts ∈ t.prom ∧ ThreadNP A tid (t, c.mem) (t', c.mem) ∧ ts ∉ t'.prom

/-- (S1′) The outstanding promise `ts` of thread `tid` can be brought, by a
promise-free run of thread `tid` alone that leaves memory unchanged, to a
state whose *next instruction* fulfils `ts` with a release store (against the
same memory). The run stops just before that instruction, so the
instruction's other writes (after the release store, possibly fresh) are not
part of it; `ts` is still outstanding at the end. Proved for every program
from a path to the fulfilment (`Config.advanceable_of_path`,
`Kraken/Promising/ReleasePrefix.lean`). -/
def Config.Advanceable (A : Arch) (c : Config I) (tid : Nat) (ts : Time) : Prop :=
  ∃ t t', c.threads[tid]? = some t ∧ ts ∈ t.prom ∧ ThreadNP A tid (t, c.mem) (t', c.mem) ∧ ts ∈ t'.prom ∧
    t'.RelFulfils A tid ts c.mem

/-- (S2) for one instruction outcome `o` from memory `mem`: if the promise
`ts` is still outstanding afterwards, the step appended nothing and read no
message above `ts`. -/
def StutterStep (ts : Time) (mem : Memory) (o : Outcome I) : Prop :=
  ts ∈ o.thread.prom → o.mem = mem ∧ ∀ l t v ν, TraceEv.read l t v ν ∈ o.log → t < ts

/-- `v` is a virtual configuration of `c`: the same memory, and every thread
either as in `c` or advanced along a promise-free run of its own that leaves
memory unchanged to a state whose next instruction fulfils one of its
outstanding promises with a release store (*pending at the next
instruction*). Design (V), variant (ii): a thread
with an outstanding promised release is advanced up to, not including, the
instruction that fulfils it (`Config.Advanceable`), so the release stays
outstanding in `v`; the instruction's other writes may be fresh, which is
why it is not run (`Config.AdvanceableStrict` is false in general). -/
def Config.VirtualOf (A : Arch) (c v : Config I) : Prop :=
  v.mem = c.mem ∧ v.threads.size = c.threads.size ∧
    ∀ i t, c.threads[i]? = some t → ∃ t', v.threads[i]? = some t' ∧ ThreadNP A i (t, c.mem) (t', c.mem) ∧
      (t' = t ∨ ∃ ts ∈ t'.prom, t'.RelFulfils A i ts c.mem)

theorem Config.VirtualOf.refl (A : Arch) (c : Config I) : c.VirtualOf A c :=
  ⟨rfl, rfl, fun _ t h => ⟨t, h, .refl _, .inl rfl⟩⟩

/-- A halted thread takes no step. -/
theorem ThreadNP.eq_of_halted {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory}
    {q : Thread I × Memory} (hh : t.halted = true) (h : ThreadNP A tid (t, mem) q) : q = (t, mem) := by
  cases h with
  | refl => rfl
  | step hs _ =>
    obtain ⟨outs, o, hstep, -, -⟩ := hs
    unfold Thread.halted at hh
    unfold stepOne at hstep
    simp only [Option.isNone_iff_eq_none] at hh
    simp [hh] at hstep

/-- **In a final configuration the virtual configuration is the real one**:
(V)'s conclusions about final configurations are conclusions about the
machine. -/
theorem Config.VirtualOf.eq_of_final {A : Arch} {c v : Config I} (hf : c.final = true)
    (hv : c.VirtualOf A v) : v = c := by
  obtain ⟨hm, hs, ht⟩ := hv
  have hth : v.threads = c.threads := by
    apply Array.ext_getElem?
    intro i
    cases hc : c.threads[i]? with
    | none =>
      have : c.threads.size ≤ i := by simpa using hc
      simp [Array.getElem?_eq_none (show v.threads.size ≤ i by omega)]
    | some t =>
      obtain ⟨t', hv', hr, -⟩ := ht i t hc
      have hhalt : t.halted = true := by
        obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hc
        have := (Array.all_eq_true.mp hf) i hi
        simp only [Bool.and_eq_true] at this
        exact this.1
      have := ThreadNP.eq_of_halted hhalt hr
      simp only [Prod.mk.injEq] at this
      rw [hv', this.1]
  cases v; cases c
  simp_all

/-- `c` is `c'` with the promises `P` outstanding again (same memory, same
threads; each thread of `c'` has a subset of its promises in `c`, and `P` is
exactly what is outstanding in `c` but not in `c'`). Read `c'.Unfulfils c P`
as "`c'` is `c` after its threads fulfilled `P` without changing memory":
the advance of a virtual configuration (`Config.VirtualOf`), or the
fulfilling instruction `F` of a pending release when `F` appends nothing. -/
structure Config.Unfulfils (c' c : Config I) (P : List Time) : Prop where
  mem : c'.mem = c.mem
  size : c'.threads.size = c.threads.size
  sub : ∀ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' →
    ∃ t : Thread I, c.threads[i]? = some t ∧ ∀ p ∈ t'.prom, p ∈ t.prom
  gone : ∀ ts, ts ∈ P ↔ (∃ (i : Nat) (t : Thread I), c.threads[i]? = some t ∧ ts ∈ t.prom) ∧
    ¬ ∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom

/-- The laws design (V) needs of a resource model, beyond `ResModel.Laws`.
Under (V) the open case of `Laws.promise` (a promised message that transfers
ownership: a promised release) needs no transfer law: the release event is
prepaid by `NPSafe`'s prepay conjunct (option (B)), whose proof
is the release rule's. What remains is SLR's erasure condition (3) for one
thread:

- `validate`: exempt erasure plus `mayWrite` for each of its outstanding
  non-pending promises (pending ones need none, as in the pending clause) is
  erasure without the exemption (Theorem 1′ restores full validity with it,
  from the path-relative condition (3)).

Until this structure also had `pending`, `fulfil` and the
`markPending` facts (variant (ii)); under option (B) they are lemmas of the
SLR instance (`SLR.erase_pending`, `SLR.erase_fulfil`), used inside Theorem
1′'s proof to move between the real and the virtual configuration, and the
placeholder `ResModel.EscrowLaws` is gone (fallback (iii) is the prepay
conjunct). -/
structure ResModel.PromisedRelease (M : ResModel I) (L : M.Laws) : Prop where
  validate : ∀ rF g (T : Nat → Prop) (c : Config I) tid, M.erase rF g T c →
    (∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ¬ M.pendingAt g ts → ∀ w, c.mem.get? ts = some w →
      L.mayWrite (rF tid) g w.loc) →
    M.erase rF g (fun i => T i ∧ i ≠ tid) c

/-- `c` is *live*: some final configuration (every thread halted, no
outstanding promise) is reachable from it. -/
def Config.Live (A : Arch) (fuel : Nat) (c : Config I) : Prop :=
  ∃ cf, Reachable A fuel c cf ∧ cf.final = true

/-- A notion of virtual configuration for Theorem 1′: any relation that is
the identity at final configurations, so that Theorem 1′'s conclusions at
final configurations are about the machine.

**Placeholder hook**: variant (ii) is `VirtualRel.ii`
(`Config.VirtualOf`). `Config.VirtualOfNT` (`ReleasePrefixNT.lean`; threads advanced past pending
non-temporal stores) is a further instance (`VirtualRel.nt`). Under option
(B) fallback (iii) needs no virtual memory: the virtual thread stops before
its fulfilling instruction, as in variant (ii), with the release prepaid.
Theorem 1′'s statement does not change. -/
structure VirtualRel (I : ISA) where
  rel : Config I → Config I → Prop
  refl : ∀ c, rel c c
  eq_of_final : ∀ c v, c.final = true → rel c v → v = c

/-- Variant (ii): `Config.VirtualOf`. -/
def VirtualRel.ii (A : Arch) : VirtualRel I where
  rel c v := c.VirtualOf A v
  refl := Config.VirtualOf.refl A
  eq_of_final _ _ hf hv := Config.VirtualOf.eq_of_final hf hv

/-- **Theorem 1′ for Kraken, design (V)** (`Prop`; restated,
switched to option (B)): if erasure holds initially and every thread
is non-promisingly safe, then every reachable *live* configuration has a
virtual configuration, with resources, that satisfies full erasure and in
which every thread that is done meets its postcondition. By
`VirtualRel.eq_of_final`, at a final configuration this is a statement about
the machine: a lock's adequacy theorem (`counter = n`, at most one owner of
`W¹(counter)`) is stated at final configurations and follows by SLR's
Lemma 26/27.

Unlike `NPSafeImpliesSafe`, this is a statement about paths, not a
step-indexed predicate. At a release promise the advancing run is the run
the thread actually takes later, on a path to a final configuration, up to
the instruction that fulfils the release (a prophecy:
`Config.advanceable_of_path` replays it on the current memory; by (S2) its
steps are stutter steps). In `v` the release is then pending at the thread's
next instruction (`Config.VirtualOf`); full erasure of `v` counts, for a
pending release, the release event's resources, prepaid at promise time by
`NPSafe`'s prepay conjunct (option (B), the pending clause of the SLR
instance).
Restricting to live configurations restricts no program: every terminating
execution consists of live configurations, so the theorem is never vacuous
for one; non-terminating and doomed paths simply carry no obligation
(non-terminating executions are Stage 3's business: there the
quantification is over fair paths on which every promise is eventually
fulfilled). The restriction is what makes the prophecy well defined, and it
is the handle on R3 and R2′: on a live path every outstanding promise is
fulfilled later, with a write permission its thread owns then (`NPSafe`'s
`owns`), which replaces SLR's `canAcq` validity (erasure condition (3)): the
path-relative conditions (1) a virtual advance exists, (2) pending promises
are fulfilled later, (3) every outstanding non-pending promise is valid
(`hval` of the RMW rule included) are invariants of the proof's induction,
not hypotheses. Their machine half is proved: in a live configuration every
outstanding promise lies above its thread's `vwNew` (`Config.Live.vwNew_lt`),
so a thread that must still acquire a message written above its promise is
doomed.

Parameters and hypotheses beyond the original design's statement:

- `Vr`: the virtual-configuration relation (`VirtualRel.ii A` today);
- `H`: a **temporary scope hypothesis** on reachable configurations. The
  only admissible instances are `fun _ => True` (the goal) and, until the
  pending-NT erasure clause is proved (`Config.VirtualOfNT` exists), the NT-free
  scope `Config.NTFree` (`SLR/Theorem1.lean`; vacuous under `Arch.armv8`,
  restricts only x86 programs with `movnti`). No other program restriction;
- the initial configuration is `Config.init` of a program (so `Config.Wf`,
  `Config.MachInv`, no promises), and no promise is pending in `g`;
- the conclusion gives `M.ghostLe g g'` (world facts of the initial ghost
  state survive, for adequacy);
- the threads' tokens start clean (`NPSafe … True …`): the proof
  shows from condition (3) that every flag stays `True`, so `B` holds;
- `NPSafe` is asked only for existing threads (`tid < states.length`):
  steps keep the number of threads, and for a nonexistent `tid` `NPSafe` is
  not provable in general. -/
def NPSafeImpliesAdequateV (M : ResModel I) (A : Arch) (fuel : Nat) (Vr : VirtualRel I)
    (H : Config I → Prop) [I.LawfulState] : Prop :=
  ∀ (L : M.Laws), M.PromisedRelease L →
    ∀ (B : Config I → M.R → M.Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
      (rF : Nat → M.R) (g : M.Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → H c) →
    M.erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ¬ M.pendingAt g ts) →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafe M A B tid n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', Vr.rel c v ∧ M.erase rF' g' (fun _ => False) v ∧ M.ghostLe g g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

end Kraken.Promising
