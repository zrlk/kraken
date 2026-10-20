/-
Lifting the event-level erasure lemmas of the SLR-adapted resource model to
instruction steps: SLR's Lemma 21 frame for a single
instruction.

Erasure (`SLR.Erase`) looks at a configuration only through its memory and
the threads' promise sets. Along an instruction of thread `tid` the event
tree threads a context (`Ctx`) whose memory and promise set therefore
determine erasure: `ErAt … r g cx` is erasure of the configuration with
thread `tid`'s promises and the memory taken from `cx`, the thread holding
`r` and the ghost state being `g`. A rule for an instruction is an **erasure
WP over its event tree** (`EvTree.EraseWP`, recursive on the tree, following
`runTree`): reads, fences, failed exclusive stores and the read of a failed
RMW keep `(r, g)` (memory and promise set are unchanged), and each write,
store or successful RMW, must re-establish erasure for some `(r', g')`, from
erasure before it and the context invariant `Ctx.Inv`.

## Contents

- `Config.withThread_withThread`, `Config.withThread_self`,
  `Erase.congrProm`, `Erase.withThread_prom`: erasure depends only on memory
  and promise sets.
- `ErAt`, `EvTree.EraseWP`, `runTree_eraseWP` (**the frame**: a run of an
  event tree from a context with erasure and `Ctx.Inv` ends with erasure and
  the WP's postcondition).
- `Erase.npStep`: **the per-instruction lemma** in the form Theorem 1′ /
  NPSafe consume (`NPStepBy`, `Config.MachInv`); `Erase.npStep_silent`: an
  instruction that changes neither memory nor the thread's promises keeps
  `(r, g)` (loads, acquire loads, fences, failed CAS, register operations).
-/
import Kraken.Promising.SLR.Invariants

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem Config.withThread_withThread (c : Config I) (tid : Nat) (t₁ t₂ : Thread I) (m₁ m₂ : Memory) :
    (c.withThread tid t₁ m₁).withThread tid t₂ m₂ = c.withThread tid t₂ m₂ := by
  simp only [Config.withThread, Config.mk.injEq, and_true]
  apply Array.ext_getElem?
  intro i
  simp only [Array.set!, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  split <;> rfl

theorem Config.withThread_self (c : Config I) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    c.withThread tid t c.mem = c := by
  have hth : (c.withThread tid t c.mem).threads = c.threads := by
    apply Array.ext_getElem?
    intro i
    rw [Config.withThread_get? c t c.mem (lt_size_of_get? ht)]
    split
    · next h => subst h; exact ht.symm
    · rfl
  cases c
  simp only [Config.withThread] at hth ⊢
  rw [hth]

theorem readSuccs_memProm (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.2.2.mem = c.mem ∧ x.2.2.prom = c.prom := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · by_cases hp : (c.mem.writeIn l t (max (max iv.addrR (max c.views.vrNew
        (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0))) (c.views.getCoh l)) ||
        c.prom.contains t) = true
    · rw [ite_eq_left hp] at ht; cases ht
    · rw [ite_eq_right hp] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨rfl, rfl⟩

end Kraken.Promising

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## Erasure depends only on memory and promise sets -/

/-- Erasure transfers between configurations with the same memory, the same
number of threads and the same promise sets. -/
theorem Erase.congrProm {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c v : Config I} (E : Erase rF g T c)
    (hm : v.mem = c.mem) (hs : v.threads.size = c.threads.size)
    (hp : ∀ (i : Nat) (t' : Thread I), v.threads[i]? = some t' → ∃ t : Thread I, c.threads[i]? = some t ∧ t.prom = t'.prom)
    (hp' : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → ∃ t' : Thread I, v.threads[i]? = some t' ∧ t'.prom = t.prom) :
    Erase rF g T v := by
  have hsub : PromSub c v := ⟨hm, hs, fun i t' hi => by
    obtain ⟨t, ht, he⟩ := hp i t' hi
    exact ⟨t, ht, fun p h => he ▸ h⟩⟩
  have hout : ∀ ts, Outstanding c ts → Outstanding v ts := by
    rintro ts ⟨i, t, ht, hts⟩
    obtain ⟨t', ht', he⟩ := hp' i t ht
    exact ⟨i, t', ht', he ▸ hts⟩
  exact E.fulfil hsub (fun ts ho hn => absurd (hout ts ho) hn)
    (fun ts => ⟨fun h => ⟨h, hout ts (E.pend ts h).2⟩, fun h => h.1⟩)

/-- Replacing thread `tid` by a thread with the same promise set keeps
erasure. -/
theorem Erase.withThread_prom {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat}
    {t₁ t₂ : Thread I} {m : Memory} (E : Erase rF g T (c.withThread tid t₁ m)) (hn : tid < c.threads.size)
    (h : t₂.prom = t₁.prom) : Erase rF g T (c.withThread tid t₂ m) := by
  refine E.congrProm rfl (by simp only [Config.withThread_size]) (fun i t' hi => ?_) (fun i t hi => ?_)
  · rw [Config.withThread_get? c t₂ m hn] at hi
    rw [Config.withThread_get? c t₁ m hn]
    split at hi
    · cases hi; exact ⟨t₁, by rw [ite_eq_left ‹_›], h.symm⟩
    · exact ⟨t', by rw [ite_eq_right ‹_›]; exact hi, rfl⟩
  · rw [Config.withThread_get? c t₁ m hn] at hi
    rw [Config.withThread_get? c t₂ m hn]
    split at hi
    · cases hi; exact ⟨t₂, by rw [ite_eq_left ‹_›], h⟩
    · exact ⟨t, by rw [ite_eq_right ‹_›]; exact hi, rfl⟩

/-! ## Erasure along an instruction -/

/-- Erasure at the context `cx` of an instruction of thread `tid` (state `t`
in `c`): the configuration with `tid`'s promise set and the memory of `cx`,
`tid` holding `r`, ghost state `g`. -/
def ErAt (rF : Nat → Res) (T : Nat → Prop) (c : Config I) (t : Thread I) (tid : Nat) (r : Res) (g : Ghost)
    (cx : Ctx) : Prop :=
  Erase (setRes rF tid r) g T (c.withThread tid { t with prom := cx.prom } cx.mem)

theorem ErAt.congr {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat} {r : Res}
    {g : Ghost} {cx cx' : Ctx} (h : ErAt rF T c t tid r g cx) (hm : cx'.mem = cx.mem) (hp : cx'.prom = cx.prom) :
    ErAt rF T c t tid r g cx' := by
  unfold ErAt at *; rw [hm, hp]; exact h

/-- The xcl-failure context of `runTree`'s `store` case. -/
abbrev xclFailCtx (cx : Ctx) (l : Loc) : Ctx :=
  { cx with views := { cx.views with xclb := none }, succView := 0, log := cx.log ++ [.xclFail l] }

/-- The context after an RMW's write (`runTree`). -/
abbrev rmwAfter (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) : Ctx :=
  if A.rmwFence then fenceStep (rmwPost A k noRet l cx) .sy else rmwPost A k noRet l cx

/-- The context of an RMW's read (`runTree`). -/
abbrev fenceOptCtx (A : Arch) (cx : Ctx) : Ctx := if A.rmwFence then fenceStep cx .sy else cx

/-- **Erasure WP over an event tree**: what a
rule for an instruction must establish along its event tree so that erasure
holds after it with resource and ghost satisfying `Post`. Reads, fences,
failed exclusive stores and the read of an RMW whose operation fails (a
failed CAS: no write, no claim) keep `(r, g)`. Every write (a store, or the
write of a successful RMW after its read) must re-establish erasure for some
`(r', g')`, given erasure before it and the context invariant `Ctx.Inv`
(which gives `OwnSeen` for an RMW's read, `rmw_event`). A store is required
for every `writeSuccs` successor, also of an unpaired exclusive store, which
`runTree` drops (an over-approximation; LL/SC is deferred in the logic). -/
def _root_.Kraken.Promising.EvTree.EraseWP (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop)
    (c : Config I) (t : Thread I) {σ : Type} (Post : σ → Res → Ghost → Ctx → Prop) :
    EvTree σ → Res → Ghost → Ctx → Prop
  | .done s, r, g, cx => Post s r g cx
  | .fault _, _, _, _ => True
  | .choose _ k, r, g, cx => ∀ i, EvTree.EraseWP A tid iv rF T c t Post (k i) r g cx
  | .load k xcl l ret, r, g, cx => ∀ x ∈ readSuccs A iv cx k xcl l,
      EvTree.EraseWP A tid iv rF T c t Post (ret x.2.1) r g x.2.2
  | .store k xcl l v ret, r, g, cx =>
      (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl l v (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
        ErAt rF T c t tid r g cx → cx.Inv tid →
        ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ EvTree.EraseWP A tid iv rF T c t Post (ret true) r' g' cx') ∧
      (xcl = true → EvTree.EraseWP A tid iv rF T c t Post (ret false) r g (xclFailCtx cx l))
  | .fence k ret, r, g, cx => EvTree.EraseWP A tid iv rF T c t Post (ret ()) r g (fenceStep cx k)
  | .rmw k noRet l op ret, r, g, cx =>
      ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
        (op x.2.1 = none → EvTree.EraseWP A tid iv rF T c t Post (ret x.2.1) r g (fenceOptCtx A x.2.2)) ∧
        ∀ new, op x.2.1 = some new →
          ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
            ErAt rF T c t tid r g x.2.2 → cx.Inv tid →
            ∃ r' g', ErAt rF T c t tid r' g' cx' ∧
              EvTree.EraseWP A tid iv rF T c t Post (ret x.2.1) r' g' (rmwAfter A k noRet l cx')

section Frame

variable (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I) (t : Thread I)

theorem fenceStep_prom (cx : Ctx) (k : FenceKind) : (fenceStep cx k).prom = cx.prom :=
  (fenceStep_fields cx k).2.2.2.2.1

theorem fenceOptCtx_memProm (cx : Ctx) : (fenceOptCtx A cx).mem = cx.mem ∧ (fenceOptCtx A cx).prom = cx.prom := by
  unfold fenceOptCtx; split
  · exact ⟨fenceStep_mem cx .sy, fenceStep_prom cx .sy⟩
  · exact ⟨rfl, rfl⟩

theorem rmwAfter_memProm (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) :
    (rmwAfter A k noRet l cx).mem = cx.mem ∧ (rmwAfter A k noRet l cx).prom = cx.prom := by
  have h1 : (rmwPost A k noRet l cx).prom = cx.prom := by unfold rmwPost; split <;> rfl
  unfold rmwAfter; split
  · exact ⟨(fenceStep_mem _ .sy).trans (rmwPost_mem A k noRet l cx), (fenceStep_prom _ .sy).trans h1⟩
  · exact ⟨rmwPost_mem A k noRet l cx, h1⟩

/-- **The frame** (SLR's Lemma 21 for one instruction): a run of an event
tree from a context with erasure, the context invariant and the erasure WP
ends in a context with erasure, for some `(r', g')` satisfying the WP's
postcondition. -/
theorem runTree_eraseWP {σ : Type} (Post : σ → Res → Ghost → Ctx → Prop) (tree : EvTree σ) :
    ∀ (r : Res) (g : Ghost) (cx : Ctx) (s : σ) (cx' : Ctx), .ok (s, cx') ∈ runTree A tid iv cx tree →
      ErAt rF T c t tid r g cx → cx.Inv tid → tree.EraseWP A tid iv rF T c t Post r g cx →
      ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ Post s r' g' cx' := by
  induction tree with
  | done s0 =>
    intro r g cx s cx' h E _ hw
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r, g, E, hw⟩
  | fault m => intro r g cx s cx' h; simp [runTree] at h
  | choose n k ih =>
    intro r g cx s cx' h E hi hw
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i r g cx s cx' h E hi (hw i)
  | load k xcl l ret ih =>
    intro r g cx s cx' h E hi hw
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    exact ih x.2.1 r g x.2.2 s cx' h (E.congr hm hp) (readSuccs_inv A tid iv hx hi).1 (hw x hx)
  | store k xcl l v ret ih =>
    intro r g cx s cx' h E hi hw
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      obtain ⟨r', g', E', hw'⟩ := hw.1 c0 hc0 E hi
      exact ih true r' g' c0 s cx' h E' (writeSuccs_inv A tid _ hc0 hi).1 hw'
    · rw [List.mem_ite_nil_right] at h
      have hi' : (xclFailCtx cx l).Inv tid := (hi.of_views (c' := xclFailCtx cx l) rfl rfl rfl).1
      exact ih false r g _ s cx' h.2 (E.congr rfl rfl) hi' (hw.2 h.1)
  | fence k ret ih =>
    intro r g cx s cx' h E hi hw
    simp only [runTree] at h
    exact ih () r g _ s cx' h (E.congr (fenceStep_mem cx k) (fenceStep_prom cx k)) (fenceStep_inv tid hi k).1 hw
  | rmw k noRet l op ret ih =>
    intro r g cx s cx' h E hi hw
    simp only [runTree] at h
    have hi1 := (fenceOpt_inv tid hi A.rmwFence .sy).1
    obtain ⟨hm1, hp1⟩ := fenceOptCtx_memProm A cx
    change Except.ok (s, cx') ∈ (readSuccs A iv (fenceOptCtx A cx)
      (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet).flatMap _ at h
    rw [List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A iv hx
    have hi2 := (readSuccs_inv A tid iv hx hi1).1
    have E2 : ErAt rF T c t tid r g x.2.2 := E.congr (hm2.trans hm1) (hp2.trans hp1)
    obtain ⟨hwn, hws⟩ := hw x hx
    obtain ⟨tr, old, c2⟩ := x
    simp only at h hwn hws E2 hi2
    split at h
    · next hop =>
      obtain ⟨hm3, hp3⟩ := fenceOptCtx_memProm A c2
      exact ih old r g _ s cx' h (E2.congr hm3 hp3) (fenceOpt_inv tid hi2 A.rmwFence .sy).1 (hwn hop)
    · next new hop =>
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change Except.ok (s, cx') ∈ runTree A tid iv (rmwAfter A k noRet l c3) (ret old) at h
      obtain ⟨r', g', E3, hw3⟩ := hws new hop c3 hc3 E2 hi
      obtain ⟨hm4, hp4⟩ := rmwAfter_memProm A k noRet l c3
      have hi3 := (writeSuccs_inv A tid _ hc3 hi2).1
      have hi4 : (rmwAfter A k noRet l c3).Inv tid := by
        unfold rmwAfter
        exact (fenceOpt_inv tid (rmwPost_inv A tid hi3 k noRet l).1 A.rmwFence .sy).1
      exact ih old r' g' _ s cx' h (E3.congr hm4 hp4) hi4 hw3

end Frame

/-! ## The per-instruction lemma -/

/-- The context `stepOne` starts an instruction of `t` in, against `mem`. -/
abbrev ctx₀ (t : Thread I) (tid : Nat) (mem : Memory) : Ctx :=
  { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }

/-- **Erasure across one instruction**: the
form Theorem 1′ and NPSafe's step consume. If erasure holds before an
instruction step of thread `tid` (`NPStepBy`) of a configuration satisfying
the machine invariants, with `tid` holding `r` and ghost `g`, and the rule
for the instruction establishes the erasure WP of its event tree with
postcondition `Post`, then erasure holds after the step for some `(r', g')`
satisfying `Post` (at the instruction's final ISA state and context). -/
theorem Erase.npStep {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {tid : Nat}
    {r : Res} {Post : I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g T c) (hs : NPStepBy A tid c c')
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWP A tid (instrViews t (I.deps t.st)) rF T c t Post r g (ctx₀ t tid c.mem)) :
    ∃ st r' g' cx', Post st r' g' cx' ∧ Erase (setRes rF tid r') g' T c' := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hstep, ho, he⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hn := lt_size_of_get? ht
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨res, hr, ho⟩ := ho
    cases res with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, cx'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have E0 : ErAt rF T c t tid r g (ctx₀ t tid c.mem) := by
        unfold ErAt
        rw [Config.withThread_self c ht]
        exact E
      obtain ⟨r', g', E', hpost⟩ := runTree_eraseWP A tid _ rF T c t Post tree r g _ st cx' hr E0
        (hinv.ctxInv ht _) (hwp t tree ht hex)
      refine ⟨st, r', g', cx', hpost, ?_⟩
      exact Erase.withThread_prom E' hn (finishInstr_relKey hth).1

/-- **An instruction that changes neither memory nor the thread's promise
set keeps erasure with the same resources** (loads, acquire loads, fences,
a failed CAS, register operations): `Erase.sameProm` at instruction level. -/
theorem Erase.npStep_silent {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {tid : Nat}
    (E : Erase rF g T c) (hs : NPStepBy A tid c c') (hm : c'.mem = c.mem)
    (hp : ∀ t t', c.threads[tid]? = some t → c'.threads[tid]? = some t' → t'.prom = t.prom) : Erase rF g T c' := by
  obtain ⟨t, t', mem', ht, -, rfl⟩ := hs
  have hn := lt_size_of_get? ht
  simp only [Config.withThread] at hm
  subst hm
  have ht' : (c.withThread tid t' c.mem).threads[tid]? = some t' := by
    rw [Config.withThread_get? c t' c.mem hn, ite_eq_left rfl]
  exact E.sameProm ht (hp t t' ht ht')

end Kraken.Promising.SLR
