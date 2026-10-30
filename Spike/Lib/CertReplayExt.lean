/-
**Append-free certification survives memory extension** (`certOkCNA_memExt`).

A certifying run that never appends (`CertOkCNA`) replays verbatim on any
extension `M'` of its memory `M` (`M.Prefix M'`): each of its reads reads the
same message (`Sim.readSuccs_memExt`: the messages of `M' ∖ M` lie above every
bound of a context bounded by `|M|`), and each of its writes fulfils a promise
in `M` with the same `atomic` check (`Memory.Prefix.get?`,
`Memory.Prefix.atomic_eq`). An append would not replay (the fresh timestamp
`|M| + 1` is taken in `M'`), which is why `CertOkC` does not transport this
way. No promise-freedom and no side condition on `M' ∖ M` is needed.

- `runTree_withMem`: a run of an event tree that does not append, from a
  bounded context, is a run from the same context on `M'`, ending in the same
  context on `M'`.
- `stepC_withMem`, `threadNPC_withMem`: the same for one certification step and
  for a certification run that ends at its start memory.
-/
import Spike.Lib.CertReplay
import Kraken.Promising.SLR.Sim.Instances
import Scc.Sem.CertStep

namespace Spike.Lib.CertReplay

open Kraken Kraken.Promising Scc.Sem

/-! ## Contexts on a larger memory -/

theorem fenceStep_withMem (c : Ctx) (k : FenceKind) (M' : Memory) :
    fenceStep { c with mem := M' } k = { fenceStep c k with mem := M' } := by
  cases k <;> rfl

theorem fenceOpt_withMem (c : Ctx) (b : Bool) (k : FenceKind) (M' : Memory) :
    (if b then fenceStep { c with mem := M' } k else { c with mem := M' }) =
      { (if b then fenceStep c k else c) with mem := M' } := by
  cases b
  · rfl
  · exact fenceStep_withMem c k M'

theorem rmwPost_withMem (A : Arch) (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) (M' : Memory) :
    rmwPost A k noRet l { c with mem := M' } = { rmwPost A k noRet l c with mem := M' } := by
  unfold rmwPost
  cases (A.rmwKind k == .acqRel && !noRet) <;> rfl

private theorem getLastD_le' {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) :
    ∀ d, d ≤ n → xs.getLastD d ≤ n := by
  induction xs with
  | nil => intro d hd; exact hd
  | cons a l ih =>
    intro d _
    rw [List.getLastD_cons]
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) a (h a List.mem_cons_self)

/-- A prefix that is no shorter is the memory itself. -/
theorem Memory.Prefix.eq_of_last_le {M N : Memory} (h : M.Prefix N) (hl : N.last ≤ M.last) : N = M := by
  have hlen : M.msgs.toList.length = N.msgs.toList.length := by
    have := h.last_le
    simp only [Memory.last, ← Array.length_toList] at this hl
    exact Nat.le_antisymm this hl
  have he := h.2.eq_of_length hlen
  exact (Memory.Prefix.antisymm h ⟨h.1.symm, he ▸ List.prefix_refl _⟩).symm

section Rules

variable {A : Arch} {tid : Nat} {iv : InstrViews} {M' : Memory}

/-- **A write that does not append** fulfils a promise; it is the same
fulfilment on any extension of the memory. -/
theorem writeSuccs_withMem {xr : View} {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (hM : c.mem.Prefix M')
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hl : c'.mem.last = c.mem.last) :
    c'.mem = c.mem ∧ { c' with mem := M' } ∈ writeSuccs A tid iv { c with mem := M' } k xcl l v tr extra xr := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, ht, w, hw, h1, h2, h3, ⟨hlt, hat⟩, rfl⟩ | ⟨-, rfl⟩
  · have htl := c.mem.last_le_of_get?_eq_some hw
    refine ⟨rfl, (mem_writeSuccs A tid).mpr (.inl ⟨t, ht, w, ?_, h1, h2, h3, ⟨hlt, ?_⟩, rfl⟩)⟩
    · show M'.get? t = some w
      rw [hM.get? htl]; exact hw
    · intro a ha
      obtain ⟨h1', h2'⟩ := hat a ha
      refine ⟨h1', ?_⟩
      show M'.atomic l tid a t = true
      rw [hM.atomic_eq h1' htl]; exact h2'
  · exfalso
    have : (c.mem.append { loc := l, val := v, tid }).1.last = c.mem.last := hl
    rw [Memory.last_append] at this
    exact Nat.succ_ne_self _ this

/-- **A run that does not append replays on a larger memory**: from a
bounded context, a run of `tree` whose final memory is no longer than the
initial one is a run from the same context on `M'`, ending in the same final
context on `M'`. -/
theorem runTree_withMem {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c2 : Ctx), c.Bnd → iv.Le c.mem.last → c.mem.Prefix M' →
      .ok (s, c2) ∈ runTree A tid iv c tree → c2.mem.last ≤ c.mem.last →
      .ok (s, { c2 with mem := M' }) ∈ runTree A tid iv { c with mem := M' } tree := by
  induction tree with
  | done s0 =>
    intro c s c2 _ _ _ h _
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [runTree]
  | fault msg =>
    intro c s c2 _ _ _ h _
    simp [runTree] at h
  | choose n k ih =>
    intro c s c2 hb hiv hM h hl
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    exact ⟨i, hi, ih i c s c2 hb hiv hM h hl⟩
  | load k xcl l ret ih =>
    intro c s c2 hb hiv hM h hl
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hr := readSuccs_bnd A iv hb hiv h0
    have hm0 : c0.mem = c.mem := hr.2.2
    refine ⟨(t, v, { c0 with mem := M' }), Sim.readSuccs_memExt A hb hiv hM h0, ?_⟩
    exact ih v c0 s c2 hr.1 (by rw [hm0]; exact hiv) (by rw [hm0]; exact hM) h (by rw [hm0]; exact hl)
  | store k xcl l v ret ih =>
    intro c s c2 hb hiv hM h hl
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · left
      rw [List.mem_ite_nil_left, List.mem_flatMap] at h ⊢
      obtain ⟨hp, c0, hc0, h⟩ := h
      refine ⟨hp, ?_⟩
      obtain ⟨hb0, hl0⟩ := writeSuccs_bnd A tid _ hb (hiv.forStore c.stores) (Nat.zero_le _) hc0
      have hl2 := (runTree_bnd A tid iv _ c0 s c2 hb0 (hiv.mono hl0) h).2
      have heq : c0.mem.last = c.mem.last := Nat.le_antisymm (Nat.le_trans hl2 hl) hl0
      obtain ⟨hm0, hc0'⟩ := writeSuccs_withMem hM hc0 heq
      exact ⟨_, hc0', ih true c0 s c2 hb0 (by rw [hm0]; exact hiv) (by rw [hm0]; exact hM) h
        (by rw [hm0]; exact hl)⟩
    · right
      rw [List.mem_ite_nil_right] at h ⊢
      refine ⟨h.1, ?_⟩
      have h0 : Ctx.Bnd
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        ⟨hb.views.xclbNone, hb.loadViews, Nat.zero_le _⟩
      exact ih false _ s c2 h0 hiv hM h.2 hl
  | fence k ret ih =>
    intro c s c2 hb hiv hM h hl
    simp only [runTree] at h ⊢
    have hm := fenceStep_mem c k
    rw [fenceStep_withMem]
    exact ih () _ s c2 (fenceStep_bnd hb k) (by rw [hm]; exact hiv) (by rw [hm]; exact hM) h
      (by rw [hm]; exact hl)
  | rmw k noRet l op ret ih =>
    intro c s c2 hb hiv hM h hl
    simp only [runTree] at h ⊢
    rw [fenceOpt_withMem]
    obtain ⟨hb1, hm1⟩ := fenceOpt_bnd hb A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hb1 hm1 ⊢
    rw [List.mem_flatMap] at h ⊢
    obtain ⟨⟨tr, old, c2'⟩, h2, h⟩ := h
    have hiv1 : iv.Le c1.mem.last := by rw [hm1]; exact hiv
    have hr := readSuccs_bnd A iv hb1 hiv1 h2
    have hm2 : c2'.mem = c.mem := hr.2.2.trans hm1
    refine ⟨(tr, old, { c2' with mem := M' }), Sim.readSuccs_memExt A hb1 hiv1 (by rw [hm1]; exact hM) h2, ?_⟩
    simp only at h ⊢
    split at h
    · rw [fenceOpt_withMem]
      obtain ⟨hb3, hm3⟩ := fenceOpt_bnd hr.1 A.rmwFence .sy
      exact ih old _ s c2 hb3 (by rw [hm3, hm2]; exact hiv) (by rw [hm3, hm2]; exact hM) h
        (by rw [hm3, hm2]; exact hl)
    · rw [List.mem_flatMap] at h ⊢
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c2) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      obtain ⟨hb3, hl3⟩ := writeSuccs_bnd A tid iv hr.1 (by rw [hm2]; exact hiv)
        (getLastD_le' hr.1.loadViews 0 (Nat.zero_le _)) hc3
      obtain ⟨hb4, hm4⟩ := rmwPost_bnd A hb3 k noRet l
      obtain ⟨hb5, hm5⟩ := fenceOpt_bnd hb4 A.rmwFence .sy
      have hiv5 : iv.Le (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy
          else rmwPost A k noRet l c3).mem.last := by
        rw [hm5, hm4]; exact hiv.mono (by rw [← hm2]; exact hl3)
      have hl2 := (runTree_bnd A tid iv _ _ s c2 hb5 hiv5 h).2
      rw [hm5, hm4] at hl2
      have heq : c3.mem.last = c2'.mem.last :=
        Nat.le_antisymm (by rw [hm2]; exact Nat.le_trans hl2 hl) hl3
      obtain ⟨hm3', hc3'⟩ := writeSuccs_withMem (by rw [hm2]; exact hM) hc3 heq
      refine ⟨{ c3 with mem := M' }, hc3', ?_⟩
      change .ok (s, { c2 with mem := M' }) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l { c3 with mem := M' }) .sy
          else rmwPost A k noRet l { c3 with mem := M' }) (ret old)
      rw [rmwPost_withMem, fenceOpt_withMem]
      exact ih old _ s c2 hb5 hiv5 (by rw [hm5, hm4, hm3', hm2]; exact hM) h
        (by rw [hm5, hm4, hm3', hm2]; exact hl)

end Rules

/-! ## Threads -/

variable {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}

/-- **A certification step that does not append replays on a larger
memory**, to the same thread. -/
theorem stepC_withMem {t t1 : Thread I} {mem mem1 M' : Memory} (hb : t.Bnd mem.last) (hM : mem.Prefix M')
    (hs : ThreadStepC A cs tid (t, mem) (t1, mem1)) (hl : mem1.last ≤ mem.last) :
    ThreadStepC A cs tid (t, M') (t1, M') := by
  obtain ⟨outs, o, hso, ho, he⟩ := hs
  obtain ⟨tree, st, c', hex, hr, hth, hm⟩ := stepOneWith_runOut A hso ho
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hc : Ctx.Bnd (Live.TicketStep.ctx0 tid t mem) :=
    ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hr' := runTree_withMem (M' := M') tree _ st c' hc (instrViews_le hb.regs _) hM hr
    (by rw [← hm]; exact hl)
  unfold ThreadStepC CertSem.step stepOneWithD
  simp only [hex]
  refine ⟨_, ⟨o.thread, M', c'.promisedNow, c'.log⟩, rfl, ?_, rfl⟩
  rw [List.mem_flatMap]
  refine ⟨.ok (st, { c' with mem := M' }), hr', ?_⟩
  simp only [List.mem_map, Except.ok.injEq]
  exact ⟨o.thread, hth, rfl⟩

/-- **A certification run that ends at its start memory replays on a larger
memory** (it never appended: memory only grows along a run). -/
theorem threadNPC_withMem {M' : Memory} {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) :
    x.1.Bnd x.2.last → x.2.Prefix M' → y.2.last ≤ x.2.last → ThreadNPC A cs tid (x.1, M') (y.1, M') := by
  induction hr with
  | refl x => intro _ _ _; exact .refl _
  | @step x z y hs hr ih =>
    intro hb hM hl
    have hxz : x.2.Prefix z.2 := threadNPC_prefix A (.step hs (.refl _))
    have hzy := threadNPC_prefix A hr
    have hz : z.2 = x.2 := Memory.Prefix.eq_of_last_le hxz (Nat.le_trans hzy.last_le hl)
    have hs' := stepC_withMem (M' := M') hb hM hs (by rw [hz]; exact Nat.le_refl _)
    obtain ⟨outs, o, hso, ho, hze⟩ := hs
    have hbz : z.1.Bnd z.2.last := by rw [hze]; exact (stepOneWith_bnd A hso ho hb).1
    exact .step hs' (ih hbz (by rw [hz]; exact hM) (by rw [hz]; exact hl))

/-- **Append-free certification survives memory extension.** -/
theorem certOkCNA_memExt {t : Thread I} {M M' : Memory} (hb : t.Bnd M.last) (hM : M.Prefix M')
    (h : CertOkCNA A cs tid t M) : CertOkCNA A cs tid t M' :=
  let ⟨t', hr, he⟩ := h
  ⟨t', threadNPC_withMem hr hb hM (Nat.le_refl _), he⟩

/-- info: 'Spike.Lib.CertReplay.certOkCNA_memExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certOkCNA_memExt

end Spike.Lib.CertReplay
