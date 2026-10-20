import WeakCore.TermRun

/-!
# TermViewInv: words' views stay below their read timestamps

The machine facts behind `TermSeenHid.EnvVR`, as a run invariant (`ViewInv`, machine-only):

* (M) `MsgV`: every message's view is at most its index;
* (W) `WV`: every word of every frame's environment has `view ≤ rts ≤ mem.size`;
* (V) `VSB`: the thread's scalar views are at most `mem.size`.

This file: the definitions and the promise-machine rules (`stepLoad`, `stepStore`,
`stepRmw`, the pair rules, `stepFence`) and the term layer's memory primitives.
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A word whose view is at most its read timestamp, at most `n`. -/
def WV (n : Nat) (w : Word) : Prop := w.view ≤ w.rts ∧ w.rts ≤ n

/-- The scalar views of a view state are at most `n`. -/
def VSB (n : Nat) (vs : VState) : Prop :=
  vs.vRd ≤ n ∧ vs.vWr ≤ n ∧ vs.vCtrl ≤ n ∧ vs.vPreBase ≤ n ∧ vs.vRelSt ≤ n

/-- Every message's view is at most its index. -/
def MsgV (mem : Memory) : Prop := ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.view ≤ t

/-- A term-layer state: `MsgV` and `VSB` at its memory's size. -/
def StV (s : St) : Prop := MsgV s.mem ∧ VSB s.mem.size s.vs

def WsV (n : Nat) (ws : List Word) : Prop := ∀ w ∈ ws, WV n w

def EnvV (n : Nat) (env : Env) : Prop := ∀ e ∈ env, WsV n e.2.2

theorem WV.mono {n n' : Nat} {w : Word} (h : WV n w) (hn : n ≤ n') : WV n' w :=
  ⟨h.1, Nat.le_trans h.2 hn⟩

theorem WsV.mono {n n' : Nat} {ws : List Word} (h : WsV n ws) (hn : n ≤ n') : WsV n' ws :=
  fun w hw => (h w hw).mono hn

theorem EnvV.mono {n n' : Nat} {env : Env} (h : EnvV n env) (hn : n ≤ n') : EnvV n' env :=
  fun e he => (h e he).mono hn

theorem VSB.mono {n n' : Nat} {vs : VState} (h : VSB n vs) (hn : n ≤ n') : VSB n' vs :=
  ⟨Nat.le_trans h.1 hn, Nat.le_trans h.2.1 hn, Nat.le_trans h.2.2.1 hn, Nat.le_trans h.2.2.2.1 hn,
    Nat.le_trans h.2.2.2.2 hn⟩

theorem WV_cst (n : Nat) (v : Val) : WV n (cst v) := ⟨Nat.le_refl _, Nat.zero_le _⟩

theorem WV_msg {mem : Memory} (hm : MsgV mem) {t : Nat} (ht : t < mem.size) :
    WV mem.size ⟨(mem[t]!).val, (mem[t]!).view, t⟩ := by
  refine ⟨?_, Nat.le_of_lt ht⟩
  have e : mem[t]? = some (mem[t]!) := by
    rw [Array.getElem?_eq_getElem ht]; simp [ht]
  exact hm t _ e

theorem WsV_nil (n : Nat) : WsV n [] := fun _ h => by cases h

theorem WsV_cons {n : Nat} {w : Word} {ws : List Word} (h : WV n w) (hs : WsV n ws) : WsV n (w :: ws) :=
  fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h
    · exact hs x hx

theorem WsV_append {n : Nat} {ws us : List Word} (h : WsV n ws) (hs : WsV n us) : WsV n (ws ++ us) :=
  fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact h x hx
    · exact hs x hx

/-! ## Joins -/

theorem foldl_max_le {α : Type} (f : α → Nat) {n : Nat} :
    ∀ (l : List α) (a : Nat), a ≤ n → (∀ x ∈ l, f x ≤ n) → l.foldl (fun acc x => max acc (f x)) a ≤ n
  | [], a, ha, _ => ha
  | x :: l, a, ha, hl => by
      simp only [List.foldl_cons]
      exact foldl_max_le f l _ (Nat.max_le.2 ⟨ha, hl x (by simp)⟩) fun y hy => hl y (by simp [hy])

theorem depView_le {regs : WeakMem.Reg → Word} {n : Nat} (h : ∀ r, (regs r).view ≤ n) (deps : List WeakMem.Reg) :
    Promises.depView regs deps ≤ n :=
  foldl_max_le (fun r => (regs r).view) deps 0 (Nat.zero_le _) fun r _ => h r

theorem pairTop_le (pairs : List Ts) (t : Ts) : WeakMem.pairTop pairs t ≤ t + 1 := by
  unfold WeakMem.pairTop; split <;> simp

theorem pairTop_le' (pairs : List Ts) (t : Ts) : Promises.pairTop pairs t ≤ t + 1 := by
  unfold Promises.pairTop; split <;> simp

theorem extTs_le (vs : VState) (pairs : List Ts) (t : Ts) : WeakMem.extTs vs pairs t ≤ t + 1 := by
  unfold WeakMem.extTs; split
  · exact Nat.zero_le _
  · exact pairTop_le pairs t

/-- What a read adds to `vRd` is in range: forwarded or not, it is below the
    timestamp read or the message's view. -/
theorem rdV_le_size {vs : VState} {pairs : List Ts} {t mv n : Nat}
    (hp : Promises.pairTop pairs t ≤ t + 1) (ht : t < n) (hv : mv ≤ n) :
    Promises.rdV vs pairs t mv ≤ n :=
  Nat.le_trans (Promises.rdV_le vs pairs t mv) (Nat.max_le.2 ⟨Nat.le_trans hp ht, hv⟩)

theorem acqV_le_size {vs : VState} {pairs : List Ts} {t mv n : Nat}
    (he : WeakMem.extTs vs pairs t ≤ t + 1) (ht : t < n) (hv : mv ≤ n) :
    Promises.acqV vs pairs t mv ≤ n := by
  rcases Promises.acqV_le vs pairs t mv with h | h
  · exact Nat.le_trans h (Nat.max_le.2 ⟨hv, Nat.le_trans he ht⟩)
  · exact Nat.le_trans h (Nat.le_of_lt ht)

/-- The leading `lockFence` of an RMW keeps every view in range. -/
theorem vsb_lock {arch : Arch} {n : Nat} {x : Promises.Thread} (h : VSB n x.vs) :
    VSB n (if arch = .tso then Promises.stepFence x .sy else x).vs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  split
  · exact ⟨h1, h2, h3, Nat.max_le.2 ⟨h4, Nat.max_le.2 ⟨h1, h2⟩⟩,
      Nat.max_le.2 ⟨h5, Nat.max_le.2 ⟨h1, h2⟩⟩⟩
  · exact ⟨h1, h2, h3, h4, h5⟩

theorem lock_regs {arch : Arch} (x : Promises.Thread) :
    (if arch = .tso then Promises.stepFence x .sy else x).regs = x.regs := by
  split <;> rfl

/-! ## Registers of a term-layer machine thread -/

theorem regsOf_WV {n : Nat} {r0 r1 r2 : Word} (h0 : WV n r0) (h1 : WV n r1) (h2 : WV n r2) :
    ∀ r, WV n (regsOf r0 r1 r2 r) := by
  intro r; unfold regsOf
  split
  · exact h0
  · split
    · exact h1
    · split
      · exact h2
      · exact WV_cst n _

/-! ## Promise-machine rules -/

theorem msg_view {mem : Memory} (hm : MsgV mem) {t : Nat} (ht : t < mem.size) : (mem[t]!).view ≤ t :=
  (WV_msg hm ht).1

theorem stepLoad_V {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs)
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) :
    VSB mem.size th'.vs ∧ WV mem.size (th'.regs dst) ∧ ∀ r, r ≠ dst → th'.regs r = th.regs r := by
  unfold Promises.stepLoad at h
  simp only [List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨ht, -⟩, rfl⟩ := h
  have hv := msg_view hm ht
  have hp := pairTop_le' pairs t
  have he := extTs_le th.vs pairs t
  obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
  have hvl : (mem[t]!).view ≤ mem.size := Nat.le_trans hv (Nat.le_of_lt ht)
  refine ⟨⟨?_, h2, h3, ?_, h5⟩, ?_, ?_⟩
  · exact Nat.max_le.2 ⟨h1, rdV_le_size hp ht hvl⟩
  · simp only; split
    · exact Nat.max_le.2 ⟨h4, acqV_le_size he ht hvl⟩
    · exact h4
  · simp only [↓reduceIte]; exact WV_msg hm ht
  · intro r hr; simp [hr]

theorem stepLoadPair_V {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs)
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th d0 d1 a deps acq) :
    VSB mem.size th'.vs ∧ WV mem.size (th'.regs d0) ∧ WV mem.size (th'.regs d1) ∧
      ∀ r, r ≠ d0 → r ≠ d1 → th'.regs r = th.regs r := by
  unfold Promises.stepLoadPair at h
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨ht0, -⟩, t1, ⟨ht1, -⟩, hx⟩ := h
  split at hx
  · cases hx
  · simp only [Option.some.injEq] at hx
    subst hx
    have hv0 := msg_view hm ht0
    have hv1 := msg_view hm ht1
    have hp0 := pairTop_le' pairs t0
    have hp1 := pairTop_le' pairs t1
    have he0 := extTs_le th.vs pairs t0
    have he1 := extTs_le th.vs pairs t1
    obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
    have hvl0 : (mem[t0]!).view ≤ mem.size := Nat.le_trans hv0 (Nat.le_of_lt ht0)
    have hvl1 : (mem[t1]!).view ≤ mem.size := Nat.le_trans hv1 (Nat.le_of_lt ht1)
    refine ⟨⟨?_, h2, h3, ?_, h5⟩, ?_, ?_, ?_⟩
    · exact Nat.max_le.2 ⟨h1, Nat.max_le.2 ⟨rdV_le_size hp0 ht0 hvl0, rdV_le_size hp1 ht1 hvl1⟩⟩
    · simp only; split
      · exact Nat.max_le.2 ⟨h4, Nat.max_le.2 ⟨acqV_le_size he0 ht0 hvl0, acqV_le_size he1 ht1 hvl1⟩⟩
      · exact h4
    · simp only [↓reduceIte]; exact WV_msg hm ht0
    · simp only
      by_cases e : d1 = d0
      · subst e; simp only [↓reduceIte]; exact WV_msg hm ht0
      · simp only [e, ↓reduceIte]; exact WV_msg hm ht1
    · intro r hr0 hr1; simp [hr0, hr1]

/-- Close `max … ≤ n` goals from hypotheses. -/
macro "maxle" : tactic => `(tactic| repeat (first | assumption | exact Nat.zero_le _ | refine Nat.max_le.2 ⟨?_, ?_⟩ | exact Nat.le_trans (by assumption) (Nat.le_succ _) | exact Nat.le_trans (by assumption) (Nat.le_add_right _ 2)))

theorem MsgV_push {mem : Memory} {m : Msg} (hm : MsgV mem) (hv : m.view ≤ mem.size) : MsgV (mem.push m) := by
  intro t m' h
  rw [Array.getElem?_push] at h
  split at h
  · cases h; rename_i e; rw [e]; exact hv
  · exact hm t m' h

theorem lt_of_some {mem : Memory} {t : Nat} {m : Msg} (h : mem[t]? = some m) : t < mem.size :=
  (Array.getElem?_eq_some_iff.1 h).1

theorem storeMview_le {th : Promises.Thread} {n : Nat} (hvs : VSB n th.vs) (hr : ∀ r, (th.regs r).view ≤ n)
    (e : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) : Promises.storeMview th e deps rel ≤ n := by
  unfold Promises.storeMview
  have hd := depView_le hr deps
  have hdv : (match e with | .const _ => 0 | .reg r => (th.regs r).view) ≤ n := by
    cases e with
    | const _ => exact Nat.zero_le _
    | reg r => exact hr r
  obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
  simp only
  split <;> maxle

theorem stepStore_V {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs) (hr : ∀ r, (th.regs r).view ≤ mem.size)
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    MsgV mem' ∧ mem.size ≤ mem'.size ∧ VSB mem'.size th'.vs ∧ th'.regs = th.regs := by
  have hmv := storeMview_le hvs hr e deps rel
  obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
  unfold Promises.stepStore at h
  simp only [List.mem_append, List.mem_singleton, List.mem_filterMap] at h
  rcases h with h | ⟨t, ht, hx⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨MsgV_push hm hmv, by simp only [Array.size_push]; exact Nat.le_succ _, ?_, rfl⟩
    simp only [Array.size_push]
    have := Nat.le_succ mem.size
    refine ⟨Nat.le_trans h1 this, ?_, Nat.le_trans h3 this, Nat.le_trans h4 this, Nat.le_trans h5 this⟩
    exact Nat.max_le.2 ⟨Nat.le_trans h2 this, this⟩
  · cases hmt : mem[t]? with
    | none => rw [hmt] at hx; cases hx
    | some m =>
      rw [hmt] at hx
      dsimp only at hx
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨-, rfl, rfl⟩ := hx
      have htl := Nat.le_of_lt (lt_of_some hmt)
      exact ⟨hm, Nat.le_refl _, ⟨h1, Nat.max_le.2 ⟨h2, htl⟩, h3, h4, h5⟩, rfl⟩

theorem stepFence_V {n : Nat} {th : Promises.Thread} (h : VSB n th.vs) (f : WeakMem.Fence) :
    VSB n (Promises.stepFence th f).vs ∧ (Promises.stepFence th f).regs = th.regs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, rfl⟩
  unfold Promises.stepFence
  cases f <;> exact ⟨by maxle, by maxle, by maxle, by maxle, by maxle⟩

theorem stepStorePair_V {mem mem' : Memory} {pairs pairs' : List Ts} {th th' : Promises.Thread}
    {a : Address} {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs) (hr : ∀ r, (th.regs r).view ≤ mem.size)
    (h : Promises.stepStorePair mem pairs th a e0 e1 deps rel = (mem', pairs', th')) :
    MsgV mem' ∧ mem.size ≤ mem'.size ∧ VSB mem'.size th'.vs ∧ th'.regs = th.regs := by
  have hm0 := storeMview_le hvs hr e0 deps rel
  have hm1 := storeMview_le hvs hr e1 deps rel
  obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
  unfold Promises.stepStorePair at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  have hs1 : mem.size ≤ mem.size + 1 := Nat.le_succ _
  have hs2 : mem.size + 1 ≤ mem.size + 1 + 1 := Nat.le_succ _
  refine ⟨MsgV_push (MsgV_push hm (Nat.max_le.2 ⟨hm0, hm1⟩)) ?_, ?_, ?_, rfl⟩
  · simp only [Array.size_push]; exact Nat.le_trans (Nat.max_le.2 ⟨hm0, hm1⟩) hs1
  · simp only [Array.size_push]; exact Nat.le_trans hs1 hs2
  · simp only [Array.size_push]
    have h12 := Nat.le_trans hs1 hs2
    exact ⟨Nat.le_trans h1 h12, Nat.max_le.2 ⟨Nat.le_trans h2 h12, hs2⟩, Nat.le_trans h3 h12,
      Nat.le_trans h4 h12, Nat.le_trans h5 h12⟩

theorem stepRmw_V_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs) (hr : ∀ r, (th.regs r).view ≤ mem.size)
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    MsgV mem' ∧ mem.size ≤ mem'.size ∧ VSB mem'.size th'.vs ∧ WV mem'.size (th'.regs dst) ∧
      ∀ r, r ≠ dst → th'.regs r = th.regs r := by
  unfold Promises.stepRmwAt at h
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨ht, -⟩, hx⟩ := h
  have hv := msg_view hm ht
  have hvl : (mem[t]!).view ≤ mem.size := Nat.le_trans hv (Nat.le_of_lt ht)
  have hp : Promises.pairTop pairs t ≤ mem.size := Nat.le_trans (pairTop_le' pairs t) ht
  have he : WeakMem.extTs th.vs pairs t ≤ mem.size := Nat.le_trans (extTs_le th.vs pairs t) ht
  have hdv := depView_le hr (newv.writeDeps deps)
  have hWV := WV_msg hm ht
  have hrd : Promises.rdV th.vs pairs t (mem[t]!).view ≤ mem.size :=
    rdV_le_size (pairTop_le' pairs t) ht hvl
  have hacq : Promises.acqV th.vs pairs t (mem[t]!).view ≤ mem.size :=
    acqV_le_size (extTs_le th.vs pairs t) ht hvl
  -- What the RMW leaves in `dst`: the read's word, or after a successful
  -- non-acquire `CAS` the value alone (`Promises.rmwDst`).  In range either way.
  have hWVd : WV mem.size (Promises.rmwDst kind acq mem[t]! t) := by
    rcases Promises.Sim.rmwDst_cases kind acq mem[t]! t with he | ⟨_, _, he⟩
    · rw [he]; exact hWV
    · rw [he]; exact ⟨Nat.le_refl _, Nat.zero_le _⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
  have hsz : mem.size ≤ mem.size := Nat.le_refl _
  split at hx
  · rw [List.mem_singleton] at hx
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨hm, Nat.le_refl _, ?_, ?_, ?_⟩
    · split
      · simp only [Promises.stepFence]
        exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
      · exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
    · split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hWVd
    · intro r hr'; split <;> simp [Promises.stepFence, hr']
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · rw [List.mem_singleton] at hx
        simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        refine ⟨MsgV_push hm ?_, by simp only [Array.size_push]; exact Nat.le_succ _, ?_, ?_, ?_⟩
        · dsimp only; split <;> maxle
        · simp only [Array.size_push]
          split
          · simp only [Promises.stepFence]
            exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
          · exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
        · simp only [Array.size_push]
          exact (by split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hWVd.mono (Nat.le_succ _))
        · intro r hr'; split <;> simp [Promises.stepFence, hr']
      · cases hx
    · obtain ⟨tw, htw, hft⟩ := List.mem_filterMap.1 hx
      cases hmt : mem[tw]? with
      | none => rw [hmt] at hft; cases hft
      | some pm =>
        rw [hmt] at hft
        dsimp only at hft
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hft
        obtain ⟨-, rfl, rfl⟩ := hft
        have htl : tw ≤ mem.size := Nat.le_of_lt (lt_of_some hmt)
        refine ⟨hm, Nat.le_refl _, ?_, ?_, ?_⟩
        · split
          · simp only [Promises.stepFence]
            exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
          · exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
        · split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hWVd
        · intro r hr'; split <;> simp [Promises.stepFence, hr']

theorem stepRmw_V {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs) (hr : ∀ r, (th.regs r).view ≤ mem.size)
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    MsgV mem' ∧ mem.size ≤ mem'.size ∧ VSB mem'.size th'.vs ∧ WV mem'.size (th'.regs dst) ∧
      ∀ r, r ≠ dst → th'.regs r = th.regs r :=
  by
  have hx := stepRmw_V_at (th := if arch = .tso then Promises.stepFence th .sy else th) hm (vsb_lock hvs) (by rw [lock_regs]; exact hr) h
  rw [lock_regs] at hx
  exact hx

set_option maxHeartbeats 2000000 in
theorem stepRmwPair_V_at {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val}
    {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs) (hr : ∀ r, (th.regs r).view ≤ mem.size)
    (h : (mem', pairs', th') ∈ Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    MsgV mem' ∧ mem.size ≤ mem'.size ∧ VSB mem'.size th'.vs ∧ WV mem'.size (th'.regs d0) ∧
      WV mem'.size (th'.regs d1) ∧ ∀ r, r ≠ d0 → r ≠ d1 → th'.regs r = th.regs r := by
  unfold Promises.stepRmwPairAt at h
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨ht0, -⟩, t1, ⟨ht1, -⟩, hx⟩ := h
  have hvl0 : (mem[t0]!).view ≤ mem.size := Nat.le_trans (msg_view hm ht0) (Nat.le_of_lt ht0)
  have hvl1 : (mem[t1]!).view ≤ mem.size := Nat.le_trans (msg_view hm ht1) (Nat.le_of_lt ht1)
  have hp0 : Promises.pairTop pairs t0 ≤ mem.size := Nat.le_trans (pairTop_le' pairs t0) ht0
  have hp1 : Promises.pairTop pairs t1 ≤ mem.size := Nat.le_trans (pairTop_le' pairs t1) ht1
  have he0 : WeakMem.extTs th.vs pairs t0 ≤ mem.size := Nat.le_trans (extTs_le th.vs pairs t0) ht0
  have he1 : WeakMem.extTs th.vs pairs t1 ≤ mem.size := Nat.le_trans (extTs_le th.vs pairs t1) ht1
  have hdv := depView_le hr (n1.writeDeps (n0.writeDeps deps))
  have hW0 := WV_msg hm ht0
  have hW1 := WV_msg hm ht1
  have hrd0 : Promises.rdV th.vs pairs t0 (mem[t0]!).view ≤ mem.size :=
    rdV_le_size (pairTop_le' pairs t0) ht0 hvl0
  have hrd1 : Promises.rdV th.vs pairs t1 (mem[t1]!).view ≤ mem.size :=
    rdV_le_size (pairTop_le' pairs t1) ht1 hvl1
  have hacq0 : Promises.acqV th.vs pairs t0 (mem[t0]!).view ≤ mem.size :=
    acqV_le_size (extTs_le th.vs pairs t0) ht0 hvl0
  have hacq1 : Promises.acqV th.vs pairs t1 (mem[t1]!).view ≤ mem.size :=
    acqV_le_size (extTs_le th.vs pairs t1) ht1 hvl1
  obtain ⟨h1, h2, h3, h4, h5⟩ := hvs
  split at hx
  · cases hx
  split at hx
  · rw [List.mem_singleton] at hx
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, -, rfl⟩ := hx
    refine ⟨hm, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
    · split
      · simp only [Promises.stepFence]
        exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
      · exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
    · split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hW0
    · by_cases e : d1 = d0
      · subst e; split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hW0
      · split <;> simp only [Promises.stepFence, e, ↓reduceIte] <;> exact hW1
    · intro r hr0 hr1; split <;> simp [Promises.stepFence, hr0, hr1]
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.mem_ite_nil_right] at hx
      obtain ⟨-, hx⟩ := hx
      · rw [List.mem_singleton] at hx
        simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, -, rfl⟩ := hx
        have hs1 : mem.size ≤ mem.size + 1 := Nat.le_succ _
        have hs2 : mem.size + 1 ≤ mem.size + 1 + 1 := Nat.le_succ _
        have h12 := Nat.le_trans hs1 hs2
        refine ⟨MsgV_push (MsgV_push hm ?_) ?_, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only; split <;> maxle
        · simp only [Array.size_push]
          exact Nat.le_trans (by split <;> maxle) hs1
        · simp only [Array.size_push]; exact h12
        · simp only [Array.size_push]
          have h1' := Nat.le_trans h1 h12
          have h2' := Nat.le_trans h2 h12
          have h3' := Nat.le_trans h3 h12
          have h4' := Nat.le_trans h4 h12
          have h5' := Nat.le_trans h5 h12
          have hvl0' := Nat.le_trans hvl0 h12
          have hvl1' := Nat.le_trans hvl1 h12
          have hp0' := Nat.le_trans hp0 h12
          have hp1' := Nat.le_trans hp1 h12
          have he0' := Nat.le_trans he0 h12
          have he1' := Nat.le_trans he1 h12
          split
          · simp only [Promises.stepFence]
            exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
          · exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
        · simp only [Array.size_push]
          split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hW0.mono h12
        · simp only [Array.size_push]
          by_cases e : d1 = d0
          · subst e; split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hW0.mono h12
          · split <;> simp only [Promises.stepFence, e, ↓reduceIte] <;> exact hW1.mono h12
        · intro r hr0 hr1; split <;> simp [Promises.stepFence, hr0, hr1]
    · obtain ⟨tw, htw, hft⟩ := List.mem_filterMap.1 hx
      cases hmt : mem[tw]? with
      | none => rw [hmt] at hft; cases hft
      | some pm =>
        cases hmt1 : mem[tw + 1]? with
        | none => rw [hmt, hmt1] at hft; cases hft
        | some pm1 =>
          rw [hmt, hmt1] at hft
          dsimp only at hft
          simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hft
          obtain ⟨-, rfl, -, rfl⟩ := hft
          have htl : tw + 1 ≤ mem.size := Nat.le_of_lt (lt_of_some hmt1)
          refine ⟨hm, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
          · split
            · simp only [Promises.stepFence]
              exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
            · exact ⟨by maxle, by maxle, by maxle, by split <;> maxle, by maxle⟩
          · split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hW0
          · by_cases e : d1 = d0
            · subst e; split <;> simp only [Promises.stepFence, ↓reduceIte] <;> exact hW0
            · split <;> simp only [Promises.stepFence, e, ↓reduceIte] <;> exact hW1
          · intro r hr0 hr1; split <;> simp [Promises.stepFence, hr0, hr1]

theorem stepRmwPair_V {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val}
    {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (hm : MsgV mem) (hvs : VSB mem.size th.vs) (hr : ∀ r, (th.regs r).view ≤ mem.size)
    (h : (mem', pairs', th') ∈ Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    MsgV mem' ∧ mem.size ≤ mem'.size ∧ VSB mem'.size th'.vs ∧ WV mem'.size (th'.regs d0) ∧
      WV mem'.size (th'.regs d1) ∧ ∀ r, r ≠ d0 → r ≠ d1 → th'.regs r = th.regs r :=
  by
  have hx := stepRmwPair_V_at (th := if arch = .tso then Promises.stepFence th .sy else th) hm (vsb_lock hvs) (by rw [lock_regs]; exact hr) h
  rw [lock_regs] at hx
  exact hx

end TermViewInv
