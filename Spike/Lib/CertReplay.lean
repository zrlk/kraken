/-
**Append-free certification** (`CertOkCNA`) and the conversion from
`CertOkC` for threads whose every instruction is a release-only single
writer (`EvTree.RelW1`, `Spike/Lib/RelW1.lean`).

`CertOkC` lets the certifying run append to memory; such a run need not
replay on a larger memory (an append followed by a fulfilment can be blocked
by the new messages). `CertOkCNA` asks for a certifying run that keeps memory
unchanged: no append at all.

`certOkCNA_of_certOkC`: along a run invariant `P` on which every
instruction's tree is `RelW1`, with every promise in memory, a certifiable
thread is certifiable without appending. Argument: a step either keeps memory,
or appends; an appending `RelW1` instruction performs exactly one write (the
append) and leaves every earlier promise `p` outstanding with `p ≤ vwOld`
(`vwOld` is raised to the fresh timestamp). Such a promise is dead for a
release writer: a release write's pre-view takes `vwOld`, so it fulfils
only above `vwOld`, and `vwOld` only grows (`CtxDead`, `run_dead`). So a run
that ends with no promise reaches the empty promise set before its first
append, and the prefix up to there is append-free (`run_na`).
-/
import Spike.Lib.RelW1
import Scc.Sem.DeadProm
import Kraken.Promising.LiveSemShape

namespace Spike.Lib.CertReplay

open Kraken Kraken.Promising Scc.Sem

/-! ## Contexts: what a `RelW1` tree run does to memory, promises and `vwOld` -/

/-- Every promise of the context is in its memory. -/
def CtxLe (c : Ctx) : Prop := ∀ p ∈ c.prom, p ≤ c.mem.last

/-- Promise `p` is outstanding and at or below `vwOld`: no release write can
fulfil it any more. -/
def CtxDead (p : Time) (c : Ctx) : Prop := p ∈ c.prom ∧ p ≤ c.views.vwOld

/-- A context step that writes nothing: memory and promises kept, `vwOld`
not lowered. -/
structure Keep (c c' : Ctx) : Prop where
  mem : c'.mem = c.mem
  prom : c'.prom = c.prom
  vwOld : c.views.vwOld ≤ c'.views.vwOld

theorem Keep.refl (c : Ctx) : Keep c c := ⟨rfl, rfl, Nat.le_refl _⟩

theorem Keep.trans {c c' c'' : Ctx} (h₁ : Keep c c') (h₂ : Keep c' c'') : Keep c c'' :=
  ⟨h₂.mem.trans h₁.mem, h₂.prom.trans h₁.prom, Nat.le_trans h₁.vwOld h₂.vwOld⟩

theorem Keep.dead {c c' : Ctx} (h : Keep c c') {p : Time} (hd : CtxDead p c) : CtxDead p c' :=
  ⟨h.prom ▸ hd.1, Nat.le_trans hd.2 h.vwOld⟩

/-- A context step of a `RelW1` tree: dead promises stay dead, promises
stay in memory, and either memory is kept or every earlier promise in memory
is dead after it. -/
structure RStep (c c' : Ctx) : Prop where
  dead : ∀ p, CtxDead p c → CtxDead p c'
  le : CtxLe c → CtxLe c'
  memOr : c'.mem = c.mem ∨ ∀ p ∈ c.prom, p ≤ c.mem.last → CtxDead p c'

theorem Keep.rstep {c c' : Ctx} (h : Keep c c') : RStep c c' :=
  ⟨fun _ hd => h.dead hd, fun hl p hp => by rw [h.mem]; exact hl p (h.prom ▸ hp), .inl h.mem⟩

theorem Keep.then_rstep {c c₁ c' : Ctx} (h₁ : Keep c c₁) (h₂ : RStep c₁ c') : RStep c c' := by
  refine ⟨fun p hd => h₂.dead p (h₁.dead hd), fun hl => h₂.le (h₁.rstep.le hl), ?_⟩
  rcases h₂.memOr with e | f
  · exact .inl (e.trans h₁.mem)
  · exact .inr fun p hp hl => f p (h₁.prom ▸ hp) (h₁.mem ▸ hl)

theorem RStep.then_keep {c c₁ c' : Ctx} (h₁ : RStep c c₁) (h₂ : Keep c₁ c') : RStep c c' := by
  refine ⟨fun p hd => h₂.dead (h₁.dead p hd), fun hl => h₂.rstep.le (h₁.le hl), ?_⟩
  rcases h₁.memOr with e | f
  · exact .inl (h₂.mem.trans e)
  · exact .inr fun p hp hl => h₂.dead (f p hp hl)

private theorem mem_erase_append {p q : Time} {l : List Time} (hp : p ∈ l) : p ∈ (l ++ [q]).erase q := by
  by_cases h : p = q
  · subst h; rw [List.erase_append_left _ hp]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact (List.mem_erase_of_ne h).mpr (List.mem_append_left _ hp)

section Rules

variable {A : Arch} {tid : Nat}

theorem readSuccs_keep {iv : InstrViews} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : Keep c x.2.2 := by
  obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
  exact ⟨rfl, rfl, Nat.le_refl _⟩

theorem fenceStep_keep (c : Ctx) (k : FenceKind) : Keep c (fenceStep c k) :=
  ⟨fenceStep_mem c k, (fenceStep_fields c k).2.2.2.2.1, Nat.le_of_eq (fenceStep_fields c k).2.2.1.symm⟩

theorem fenceOpt_keep (c : Ctx) (b : Bool) (k : FenceKind) : Keep c (if b then fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact fenceStep_keep c k

theorem rmwPost_keep (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : Keep c (rmwPost A k noRet l c) := by
  unfold rmwPost
  split
  · exact ⟨rfl, rfl, Nat.le_refl _⟩
  · exact ⟨rfl, rfl, Nat.le_refl _⟩

/-- **A release write** is an `RStep`. -/
theorem writeSuccs_rstep {iv : InstrViews} {xr : View} {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {tr : Option Time} {extra : View} (hk : A.storeKind k = .rel)
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : RStep c c' := by
  rcases Live.SpinSemShape.mem_writeSuccs_c A tid iv h with
    ⟨e1, e2, e3, e4, -, -⟩ | ⟨ts, -, -, -, e3, e4, e5, e6, -, -⟩
  · have hnt : (A.storeKind k == .nt) = false := by rw [hk]; decide
    refine ⟨fun p hd => ⟨e2 ▸ mem_erase_append hd.1, Nat.le_trans hd.2 e4⟩, fun hl p hp => ?_,
      .inr fun p hp hle => ⟨e2 ▸ mem_erase_append hp, Nat.le_trans (Nat.le_succ_of_le hle) (e3 hnt)⟩⟩
    rw [e1, Memory.last_append]
    rw [e2] at hp
    rcases List.mem_append.mp (List.mem_of_mem_erase hp) with hp | hp
    · exact Nat.le_succ_of_le (hl p hp)
    · exact Nat.le_of_eq (List.mem_singleton.mp hp)
  · have hlt := e3 (by rw [hk]; decide)
    refine ⟨fun p hd => ⟨?_, Nat.le_trans hd.2 e6⟩, fun hl p hp => ?_, .inl e4⟩
    · have hne : p ≠ ts := Nat.ne_of_lt (Nat.lt_of_le_of_lt hd.2 hlt)
      rw [e5]; exact (List.mem_erase_of_ne hne).mpr hd.1
    · rw [e4]; rw [e5] at hp; exact hl p (List.mem_of_mem_erase hp)

/-- **A tree with no write** keeps memory and promises. -/
theorem noW_run {iv : InstrViews} {σ : Type} {e : EvTree σ} (h : EvTree.NoW e) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c e → Keep c c' := by
  induction h with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .refl _
  | fault m => intro c s c' h; simp [runTree] at h
  | choose _ ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h
  | load _ ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (readSuccs_keep hx).trans (ih x.2.1 x.2.2 s c' h)
  | fence _ ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (fenceStep_keep c _).trans (ih () _ s c' h)

/-- **A run of a `RelW1` tree** is an `RStep`. -/
theorem relW1_run {iv : InstrViews} {σ : Type} {e : EvTree σ} (h : EvTree.RelW1 A e) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c e → RStep c c' := by
  induction h with
  | noW h => intro c s c' hr; exact (noW_run h c s c' hr).rstep
  | choose _ ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h
  | load _ ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (readSuccs_keep hx).then_rstep (ih x.2.1 x.2.2 s c' h)
  | fence _ ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (fenceStep_keep c _).then_rstep (ih () _ s c' h)
  | store hk hn =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_rstep hk hc0).then_keep (noW_run (hn true) _ s c' h)
    · rw [List.mem_ite_nil_right] at h
      have h1 := noW_run (A := A) (tid := tid) (iv := iv) (hn false) _ s c' h.2
      exact (⟨h1.mem, h1.prom, h1.vwOld⟩ : Keep c c').rstep
  | @rmw k noRet l op ret hk hn =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := fenceOpt_keep c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_keep h2)
    simp only at h
    split at h
    · exact (h12.trans ((fenceOpt_keep c2 _ _).trans (noW_run (hn old) _ s c' h))).rstep
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact h12.then_rstep ((writeSuccs_rstep hk hc3).then_keep
        ((rmwPost_keep c3 k noRet l).trans ((fenceOpt_keep _ _ _).trans (noW_run (hn old) _ s c' h))))

end Rules

/-! ## Threads -/

variable {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}

/-- **Append-free certification under `cs`**: a promise-free solo run under
`cs` that keeps memory unchanged and empties the promise set. -/
def CertOkCNA (A : Arch) (cs : CertSem I) (tid : Nat) (t : Thread I) (mem : Memory) : Prop :=
  ∃ t', ThreadNPC A cs tid (t, mem) (t', mem) ∧ t'.prom = []

theorem CertOkCNA.certOkC {t : Thread I} {mem : Memory} (h : CertOkCNA A cs tid t mem) :
    CertOkC A cs tid t mem :=
  let ⟨t', hr, he⟩ := h; ⟨t', mem, hr, he⟩

/-- A thread with no promise is append-free certified (the empty run). -/
theorem certOkCNA_of_prom_nil {t : Thread I} {mem : Memory} (h : t.prom = []) : CertOkCNA A cs tid t mem :=
  ⟨t, .refl _, h⟩

/-- Promise `p` of thread `t` is outstanding and at or below `vwOld`. -/
def Dead (p : Time) (t : Thread I) : Prop := p ∈ t.prom ∧ p ≤ t.views.vwOld

/-- Every promise of the thread is in the memory. -/
def PromLe (x : Thread I × Memory) : Prop := ∀ p ∈ x.1.prom, p ≤ x.2.last

/-- **One instruction whose tree is `RelW1`**: dead promises stay dead,
promises stay in memory, and either memory is kept or every earlier promise
in memory is dead after it. -/
theorem stepC_rstep {x y : Thread I × Memory} (hs : ThreadStepC A cs tid x y)
    (hrel : ∀ e, cs.exec x.1.st = some e → EvTree.RelW1 A e) :
    (∀ p, Dead p x.1 → Dead p y.1) ∧ (PromLe x → PromLe y) ∧
      (y.2 = x.2 ∨ ∀ p ∈ x.1.prom, p ≤ x.2.last → Dead p y.1) := by
  obtain ⟨outs, o, hso, ho, rfl⟩ := hs
  unfold CertSem.step stepOneWithD at hso
  cases hex : cs.exec x.1.st with
  | none => rw [hex] at hso; cases hso
  | some tree =>
    rw [hex] at hso
    have hso' : _ = outs := Option.some.inj hso
    subst hso'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hR := relW1_run (hrel _ hex) _ _ _ hr
      obtain ⟨e1, e2⟩ := finishInstr_relKey hth
      have e3 : th.views.vwOld = c'.views.vwOld := by have := congrArg Views.vwOld e2; exact this
      have hD : ∀ p, CtxDead p c' → Dead p th := fun p hd => ⟨by rw [e1]; exact hd.1, by rw [e3]; exact hd.2⟩
      refine ⟨fun p hd => hD p (hR.dead p hd), fun hl p hp => hR.le hl p (by rw [← e1]; exact hp), ?_⟩
      rcases hR.memOr with h | h
      · exact .inl h
      · exact .inr fun p hp hle => hD p (h p hp hle)

section Run

variable {P : Thread I × Memory → Prop}
  (hP : ∀ x y, P x → ThreadStepC A cs tid x y → CertOkC A cs tid y.1 y.2 → P y)
  (hrel : ∀ x e, P x → cs.exec x.1.st = some e → EvTree.RelW1 A e)
include hP hrel

/-- **A dead promise blocks every certifying run** of a release writer. -/
theorem run_dead {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) :
    y.1.prom = [] → P x → ∀ p, Dead p x.1 → False := by
  induction hr with
  | refl x =>
    intro he _ p hd
    have h := hd.1
    rw [he] at h
    cases h
  | step hs hr ih =>
    intro he hx p hd
    exact ih he (hP _ _ hx hs ⟨_, _, hr, he⟩) p ((stepC_rstep hs (fun e h => hrel _ e hx h)).1 p hd)

/-- **A certifying run of a release writer empties the promise set before
it first appends.** -/
theorem run_na {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) :
    y.1.prom = [] → P x → PromLe x → ∃ t', ThreadNPC A cs tid x (t', x.2) ∧ t'.prom = [] := by
  induction hr with
  | refl x => intro he _ _; exact ⟨x.1, .refl _, he⟩
  | @step x z y hs hr ih =>
    intro he hx hl
    by_cases h0 : x.1.prom = []
    · exact ⟨x.1, .refl _, h0⟩
    have hz := hP _ _ hx hs ⟨_, _, hr, he⟩
    obtain ⟨-, hle, hm⟩ := stepC_rstep hs (fun e h => hrel _ e hx h)
    rcases hm with hm | hm
    · obtain ⟨t', hr', ht'⟩ := ih he hz (hle hl)
      rw [hm] at hr'
      exact ⟨t', .step hs hr', ht'⟩
    · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h0
      exact (run_dead hP hrel hr he hz p (hm p hp (hl p hp))).elim

/-- **Certification without appending**: along a run invariant `P` (kept by
every step that stays certifiable) on which every instruction's tree is
`RelW1`, a certifiable thread whose promises are in memory is certifiable
without appending. -/
theorem certOkCNA_of_certOkC {t : Thread I} {mem : Memory} (hx : P (t, mem))
    (hle : ∀ p ∈ t.prom, p ≤ mem.last) (hc : CertOkC A cs tid t mem) : CertOkCNA A cs tid t mem := by
  obtain ⟨t', mem', hr, he⟩ := hc
  exact run_na hP hrel hr he hx hle

end Run

end Spike.Lib.CertReplay
