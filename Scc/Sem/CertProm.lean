/-
**Certified promises, by an invariant of the certification run**
(`Scc/DESIGN.md` §9.0, *Certified promises in M1*).

A promise is certified (`CertOkC`) by a promise-free solo run of the thread
that empties its promise set. A promise leaves the set only when a write
of the run fulfils it, and a fulfilment writes exactly the promised
message's location and value (`Lower.mem_writeSuccs_iff`). So any property
`G` that every fulfilling write of the run satisfies holds of every
certified promise.

`Scc/Sem/Wide.lean` proves this per tree (`WriteCodeOn`). That quantifies
over every value a load may return, so it fails for a property of the
store address: scc code stores through locatives it has loaded. Here the
property is required only along the run, from the states of an invariant
`Q` of the thread **and memory** that the run's steps keep. With one thread
and promises never mirrored, a load's value is pinned by memory (the
latest message the thread has not promised, `stepOne_load_tlatestP`), so
the one-thread simulation relation itself is such a `Q`.

- `TreeWrite`: a write event of a tree (some path) writes `l := v`.
- `runTree_fulfil`, `stepOneWith_fulfil`: a promise that leaves the
  promise set during a run of a tree was fulfilled by one of the tree's
  writes.
- `stepOneWith_prefix`, `threadNPC_prefix`: memory only grows along a
  certification run.
- `StepG`: `Q` is kept by every certification step on a certifying run,
  and every promise such a step removes is of a message satisfying `G`.
  `certOkC_prom_good_cfg`: then every outstanding promise of a certifiable
  `Q` configuration satisfies `G`.
- `MsgsExcept`: every message of a memory, except those at the given
  timestamps (the outstanding promises), satisfies a predicate:
  `msgsExcept_promise`, `msgsExcept_fulfil`, `msgsExcept_nil`.

**The closure obligation (one thread, AArch64; Spike side).** The
statement `PromShared` asks for `G w := LocIn Λ.shared w.loc` (with
`FixG Fix m0 w.loc w.val` for the fixed runtime words). Instantiate:

```
-- (th, mem) is in the fragment: Pre at the configuration with thread th
-- and memory mem, except that the messages at th's outstanding promises
-- need not be in the layout.
def PreC (Λ P p I) (x : Thread isaLSE2 × Memory) : Prop :=
  ∃ t s, PreX Λ P p I t s ∧ t.1.threads = #[x.1] ∧ t.1.mem = x.2
-- PreX: Pre with its field `MemIn Λ mem` replaced by
--   MemInExcept Λ th mem :=
--     MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧
--     ∀ q ∈ mem.init, InitIn Λ q.1
-- (with `prom = []` it is MemIn, `msgsExcept_nil`) and with
-- MemInv (FixG Fix m0) weakened in the same way, if Pre carries it.

theorem preC_start (h : Pre Λ P p I t s) (ht : t.1.threads = #[th]) (hw : w.tid = 0)
    (hc : CertOkC Arch.armv8 (Kernel.certExec abi) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1) :
    PreC Λ P p I (Live.Sem.promThread th t.1.mem w, (t.1.mem.append w).1)
  -- Inv1.promise_cert_on (8 bytes), msgsExcept_promise

theorem preC_step :
    StepG Arch.armv8 (Kernel.certExec abi) 0 (PreC Λ P p I)
      (fun w => LocIn Λ.shared w.loc ∧ FixG Fix m0 w.loc w.val)
  -- off a system call (`certExec_of_not_atSys`) a certification step is a
  -- `stepOne` whose outcome is certified (`StepG` supplies CertOkC of the
  -- result), so the machine's instruction step; `pre_step` / the
  -- `ExtRows.out_*` rows give PreC again, and the store and RMW rows give
  -- G of the written message, which `stepOneWith_fulfil` identifies with
  -- the fulfilled one (`msgsExcept_fulfil` re-establishes MemInExcept);
  -- at a system call, the `certSuccs` returns (`Nodes.sysOk`: exit_group
  -- is a dead end; write to fd 2, futex, rt_sigaction need the sys row for
  -- every return in `Kernel.results`).

-- then PromShared:
--   certOkC_prom_good_cfg preC_step (preC_start …) hc
--     (List.mem_append_right _ (List.mem_singleton.mpr rfl)) Memory.get?_append_new
```
-/
import Scc.Sem.Wide
import Scc.Sem.Coh

namespace Scc.Sem

open Kraken Kraken.Promising

/-! ## Writes of a tree -/

/-- **Some path of the tree writes `l := v`**: a store of `v` to `l`, or an
RMW at `l` whose operation may write `v`. -/
inductive TreeWrite {σ : Type} : EvTree σ → Loc → Val → Prop
  | store {k xcl l v ret} : TreeWrite (.store k xcl l v ret) l v
  | rmw {k nr l op ret old v} : op old = some v → TreeWrite (.rmw k nr l op ret) l v
  | choose {n k i l v} : TreeWrite (k i) l v → TreeWrite (.choose n k) l v
  | load {k xcl l' ret x l v} : TreeWrite (ret x) l v → TreeWrite (.load k xcl l' ret) l v
  | storeK {k xcl l' v' ret b l v} : TreeWrite (ret b) l v → TreeWrite (.store k xcl l' v' ret) l v
  | rmwK {k nr l' op ret x l v} : TreeWrite (ret x) l v → TreeWrite (.rmw k nr l' op ret) l v
  | fence {k ret u l v} : TreeWrite (ret u) l v → TreeWrite (.fence k ret) l v

/-- A tree with no write of `l := v` writes only other location-value
pairs. -/
theorem writeTree_of_not_treeWrite {σ : Type} {l : Loc} {v : Val} :
    ∀ {t : EvTree σ}, ¬ TreeWrite t l v → WriteTree (fun l' v' => ¬ (l' = l ∧ v' = v)) t
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => writeTree_of_not_treeWrite fun h' => h (.choose h')
  | .load _ _ _ _, h => fun x => writeTree_of_not_treeWrite fun h' => h (.load h')
  | .store _ _ _ _ _, h =>
    ⟨fun ⟨hl, hv⟩ => by subst hl; subst hv; exact h .store,
      fun b => writeTree_of_not_treeWrite fun h' => h (.storeK h')⟩
  | .rmw _ _ _ _ _, h =>
    ⟨fun old v' he ⟨hl, hv⟩ => by subst hl; subst hv; exact h (.rmw he),
      fun x => writeTree_of_not_treeWrite fun h' => h (.rmwK h')⟩
  | .fence _ _, h => fun u => writeTree_of_not_treeWrite fun h' => h (.fence h')

/-- **A promise fulfilled during a run of a tree was fulfilled by one of
its writes**: if `p`, of message `w`, leaves the promise set, the tree
writes `w.loc := w.val`. -/
theorem runTree_fulfil (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ) {c : Ctx} {s : σ}
    {c' : Ctx} (hr : .ok (s, c') ∈ runTree A tid iv c tree) {p : Time} (hp : p ∈ c.prom) {w : Msg}
    (hg : c.mem.get? p = some w) (hp' : p ∉ c'.prom) : TreeWrite tree w.loc w.val :=
  Classical.byContradiction fun hn =>
    hp' (runTree_hasBad A tid iv tree (writeTree_of_not_treeWrite hn) c s c' hr p
      ⟨hp, w, hg, fun h => h ⟨rfl, rfl⟩⟩).1

/-- **A promise fulfilled by one instruction under a certification semantics was fulfilled
by one of the instruction's writes.** -/
theorem stepOneWith_fulfil {I : ISA} (A : Arch) {cs : CertSem I} {t : Thread I}
    {tid : Nat} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : cs.step A t tid mem = some outs) {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {p : Time} (hp : p ∈ t.prom) {w : Msg} (hg : mem.get? p = some w) (hp' : p ∉ o.thread.prom) :
    ∃ tree, cs.exec t.st = some tree ∧ TreeWrite tree w.loc w.val := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      refine ⟨tree, rfl, runTree_fulfil A tid _ tree hr hp hg ?_⟩
      intro hc; apply hp'; show p ∈ th.prom
      rw [(finishInstr_relKey hth).1]; exact hc

/-! ## Memory along a certification run -/

/-- **One instruction under a certification semantics only appends to memory.** -/
theorem stepOneWith_prefix {I : ISA} (A : Arch) {cs : CertSem I} {t : Thread I}
    {tid : Nat} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : cs.step A t tid mem = some outs) {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) :
    mem.Prefix o.mem := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, -, rfl⟩ := ho
      obtain ⟨hi, ws, -, hm⟩ := runTree_ext A tid _ tree _ st c' hr
      exact ⟨hi, by show mem.msgs.toList <+: c'.mem.msgs.toList; rw [hm]; exact List.prefix_append _ _⟩

/-- **A certification run only appends to memory.** -/
theorem threadNPC_prefix {I : ISA} (A : Arch) {cs : CertSem I} {tid : Nat}
    {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) : x.2.Prefix y.2 := by
  induction hr with
  | refl x => exact Memory.Prefix.refl _
  | step hs _ ih =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    exact (stepOneWith_prefix A hso ho).trans ih

/-! ## Certified promises from an invariant of the run -/

section Cfg

variable {I : ISA} (A : Arch) (cs : CertSem I) (tid : Nat)

/-- **`Q` is kept along certifying runs, and their fulfilments satisfy
`G`**: every certification step from a `Q` configuration to one that is
still certifiable (`CertOkC`) lands in `Q`, and every promise it removes
from the promise set is of a message satisfying `G`. -/
def StepG (Q : Thread I × Memory → Prop) (G : Msg → Prop) : Prop :=
  ∀ x y, Q x → ThreadStepC A cs tid x y → CertOkC A cs tid y.1 y.2 →
    Q y ∧ ∀ p ∈ x.1.prom, p ∉ y.1.prom → ∀ w, x.2.get? p = some w → G w

variable {A cs tid}

/-- **Every outstanding promise of a certifiable `Q` configuration satisfies
`G`**, when `Q` is kept along certifying runs and their fulfilments satisfy
`G` (`StepG`). -/
theorem certOkC_prom_good_cfg {Q : Thread I × Memory → Prop} {G : Msg → Prop} (hQ : StepG A cs tid Q G)
    {t : Thread I} {mem : Memory} (hq : Q (t, mem)) (hc : CertOkC A cs tid t mem) {p : Time}
    (hp : p ∈ t.prom) {w : Msg} (hg : mem.get? p = some w) : G w := by
  obtain ⟨t', mem', hr, he⟩ := hc
  suffices key : ∀ x y, ThreadNPC A cs tid x y → y.1.prom = [] → Q x → p ∈ x.1.prom →
      x.2.get? p = some w → G w from key _ _ hr he hq hp hg
  intro x y hr
  induction hr with
  | refl x => intro he _ hp _; rw [he] at hp; cases hp
  | @step x y z hs hr ih =>
    intro he hq hp hg
    obtain ⟨hqy, hful⟩ := hQ x y hq hs ⟨z.1, z.2, hr, he⟩
    by_cases hpy : p ∈ y.1.prom
    · obtain ⟨outs, o, hso, ho, rfl⟩ := hs
      have hpre := stepOneWith_prefix A hso ho
      exact ih he hqy hpy (by rw [hpre.get? (Memory.le_last_of_get? hg)]; exact hg)
    · exact hful p hp hpy w hg

end Cfg

/-! ## Messages in a region, except the outstanding promises -/

/-- **Every message of `mem`, except those at the timestamps `prom`,
satisfies `Pm`.** With `prom` a thread's outstanding promises: a message the
thread has promised but not yet written need not be in the layout. -/
def MsgsExcept (Pm : Msg → Prop) (prom : List Time) (mem : Memory) : Prop :=
  ∀ k m, mem.get? k = some m → k ∉ prom → Pm m

/-- With no outstanding promise it is every message. -/
theorem msgsExcept_nil {Pm : Msg → Prop} {mem : Memory} (h : MsgsExcept Pm [] mem) :
    ∀ k m, mem.get? k = some m → Pm m :=
  fun k m hk => h k m hk List.not_mem_nil

/-- Every message satisfying `Pm` gives `MsgsExcept` for any promises. -/
theorem MsgsExcept.of_all {Pm : Msg → Prop} {mem : Memory} (h : ∀ k m, mem.get? k = some m → Pm m)
    (prom : List Time) : MsgsExcept Pm prom mem :=
  fun k m hk _ => h k m hk

/-- **A promise step keeps `MsgsExcept`**: the appended message is
promised. -/
theorem msgsExcept_promise {Pm : Msg → Prop} {prom : List Time} {mem : Memory} (h : MsgsExcept Pm prom mem)
    (w : Msg) : MsgsExcept Pm (prom ++ [(mem.append w).2]) (mem.append w).1 := by
  intro k m hk hn
  have hne : k ≠ mem.last + 1 := fun he => hn (List.mem_append_right _ (List.mem_singleton.mpr he))
  exact h k m (CohCoversP.get?_append_ne hk hne) fun hp => hn (List.mem_append_left _ hp)

/-- **A step that only appends messages satisfying `Pm` or fulfils
promises of such messages keeps `MsgsExcept`**: every message of the new
memory outside the new promises is old and outside the old promises, a
fulfilled promise's, or a new one satisfying `Pm`. -/
theorem msgsExcept_fulfil {Pm : Msg → Prop} {prom prom' : List Time} {mem mem' : Memory}
    (h : MsgsExcept Pm prom mem) (hpre : mem.Prefix mem')
    (hful : ∀ p ∈ prom, p ∉ prom' → ∀ w, mem.get? p = some w → Pm w)
    (hnew : ∀ k m, mem'.get? k = some m → mem.last < k → k ∉ prom' → Pm m) :
    MsgsExcept Pm prom' mem' := by
  intro k m hk hn
  by_cases hle : k ≤ mem.last
  · rw [hpre.get? hle] at hk
    by_cases hp : k ∈ prom
    · exact hful k hp hn m hk
    · exact h k m hk hp
  · exact hnew k m hk (Nat.lt_of_not_le hle) hn

end Scc.Sem
