/-
**Design prototype.** The ghost steps of the ticket
dispenser (`SLR/LoadClaim.lean`) and their preservation lemmas.

- `Dispenser.handGhost g n`: the dispenser slot loses `tk n`; the thread's
  resource gains `tok o (tk n)`.
- `Dispenser.eraseHandOut`: **existing erasure survives the hand-out** (total resource
  unchanged: the token moves from a slot to the thread).
- `mayWrite_hand`, `reachB_hand`: K1 (the taking thread's reach does not
  grow: the token's slots were reachable through the dispenser's update id)
  and K2 (frames lose reach only).
- `DispOK.rmw`: after the claim of an RMW on `x` reading value `n`
  (`Erase.rmw`'s `rmwGhost`), the dispenser invariant holds with exception
  `n`, and `n` was not handed out before (`MonoX` + the read message
  unclaimed).
- `DispOK.handOut`: the hand-out removes the exception.
- **`EraseT.rmwHand`**: the composition, preservation of `EraseT` under the
  `ldadda` step (claim + hand-out).
- **`EraseT.take`** (`takeEraseLawT`): the take rule keeps `EraseT` (the
  analogue of `takeEraseLaw` for the token-guarded take).
- `DispOK.frame`: the dispenser invariant under any ghost step that keeps
  the dispenser slot, the claims of `x`, `ιD` and its predicate (stores,
  releases, RMWs on other locations).

Nothing imports this file.
-/
import Kraken.Promising.SLR.LoadClaim

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {L : List α}, (L.map f).Nodup → ∀ {a b : α}, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: L, hnd, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (hab ▸ List.mem_map.mpr ⟨b, hb', rfl⟩) hnd.1
    · exact absurd (hab.symm ▸ List.mem_map.mpr ⟨a, ha', rfl⟩) hnd.1
    · exact eq_of_nodup_map hnd.2 ha' hb' hab

namespace Dispenser

/-! ## The hand-out ghost step -/

/-- One slot under the hand-out of `tk n`: the dispenser slot drops it. -/
def handSlot (D : Dispenser) (n : Nat) (s : Slot) : Slot :=
  if D.IsDisp s then { s with res := dropTk s.res D.o (D.tk n) } else s

/-- The ghost after handing out `tk n`. -/
def handGhost (D : Dispenser) (g : Ghost) (n : Nat) : Ghost := { g with u := g.u.map (D.handSlot n) }

variable {D : Dispenser}

@[simp] theorem handSlot_key (n : Nat) (s : Slot) : (D.handSlot n s).key = s.key := by
  unfold handSlot; split <;> rfl

@[simp] theorem handSlot_id (n : Nat) (s : Slot) : (D.handSlot n s).id = s.id := by
  unfold handSlot; split <;> rfl

@[simp] theorem handSlot_wr (n : Nat) (s : Slot) : (D.handSlot n s).res.wr = s.res.wr := by
  unfold handSlot; split <;> rfl

theorem handSlot_acq_le (n : Nat) (s : Slot) (y : Loc) (j : PredId) :
    (D.handSlot n s).res.acq y j ≤ s.res.acq y j := by
  unfold handSlot; split
  · simp only [dropTk]; split <;> omega
  · exact Nat.le_refl _

theorem handSlot_of_not {n : Nat} {s : Slot} (h : ¬ D.IsDisp s) : D.handSlot n s = s := by
  simp [handSlot, h]

theorem handSlot_res_of {n : Nat} {s : Slot} (h : D.IsDisp s) :
    (D.handSlot n s).res = dropTk s.res D.o (D.tk n) := by
  simp [handSlot, h]

theorem handGhost_le (g : Ghost) (n : Nat) : g.Le (D.handGhost g n) :=
  ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩

theorem isDisp_eq {s s' : Slot} (h : D.IsDisp s) (h' : D.IsDisp s') : (s.key, s.id) = (s'.key, s'.id) := by
  rw [h.1, h.2, h'.1, h'.2]

/-- **The slots' product before and after the hand-out**. -/
theorem prod_handSlot {n : Nat} : ∀ {L : List Slot}, (L.map fun s => (s.key, s.id)).Nodup → ∀ {s₀ : Slot},
    s₀ ∈ L → D.IsDisp s₀ → s₀.res.acq D.o (D.tk n) = 1 →
    (Res.prod ((L.map (D.handSlot n)).map (·.res))).op (tok D.o (D.tk n)) = Res.prod (L.map (·.res))
  | [], _, _, h, _, _ => by cases h
  | s :: L, hnd, s₀, h₀, hd, h1 => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, Res.prod_cons]
    by_cases hs : D.IsDisp s
    · have hs₀ : s = s₀ := by
        rcases List.mem_cons.mp h₀ with h | h
        · exact h.symm
        · exfalso; apply hnd.1
          rw [isDisp_eq hs hd]; exact List.mem_map.mpr ⟨s₀, h, rfl⟩
      subst hs₀
      have hL : L.map (D.handSlot n) = L.map id :=
        List.map_congr_left fun s' hs' => handSlot_of_not fun hd' => hnd.1 (by
          rw [← isDisp_eq hd' hs]; exact List.mem_map.mpr ⟨s', hs', rfl⟩)
      rw [hL, List.map_id, handSlot_res_of hs, Res.op_assoc, Res.op_comm (Res.prod _) (tok _ _),
        ← Res.op_assoc, dropTk_op_tok h1]
    · have h₀' : s₀ ∈ L := by
        rcases List.mem_cons.mp h₀ with h | h
        · exact absurd (h ▸ hd) hs
        · exact h
      rw [handSlot_of_not hs, Res.op_assoc, prod_handSlot hnd.2 h₀' hd h1]

/-- **The total resource is unchanged by the hand-out.** -/
theorem total_hand {rF : Nat → Res} {g : Ghost} {c : Config I} {tid : Nat} {r : Res} {n : Nat}
    (hn : tid < c.threads.size) (hnd : (g.u.map fun s => (s.key, s.id)).Nodup) {s₀ : Slot} (h₀ : s₀ ∈ g.u)
    (hd : D.IsDisp s₀) (h1 : s₀.res.acq D.o (D.tk n) = 1) :
    total (setRes rF tid (r.op (tok D.o (D.tk n)))) (D.handGhost g n) c = total (setRes rF tid r) g c := by
  obtain ⟨rest, hrest⟩ := threadsRes_split rF hn
  have e0 := hrest (setRes rF tid r) fun i hi => setRes_ne rF r hi
  have e1 := hrest (setRes rF tid (r.op (tok D.o (D.tk n)))) fun i hi => setRes_ne rF _ hi
  have hS := prod_handSlot hnd h₀ hd h1
  simp only [total, Ghost.slotsRes, handGhost, e0, e1, setRes_self]
  rw [← hS]
  simp only [Res.op_assoc]
  rw [Res.op_left_comm (tok D.o (D.tk n)) rest, Res.op_comm (tok D.o (D.tk n))]

/-- **Existing erasure survives the hand-out** of `tk n` to thread `tid`.
`hP`: the dispenser's predicate accepts the reduced resource (`DispOK.dPred`).
`hval`: promise validity after the step (the dispenser lost a token, so a
chain of another thread through it may break, as for `Erase.rmw`'s claims). -/
theorem eraseHandOut {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r : Res}
    {n : Nat} (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size) {s₀ : Slot} (h₀ : s₀ ∈ g.u)
    (hd : D.IsDisp s₀) (h1 : s₀.res.acq D.o (D.tk n) = 1)
    (hP : ∀ v m V r, (g.acqPred D.ιD).P v m V r → (g.acqPred D.ιD).P v m V (dropTk r D.o (D.tk n)))
    (hval : ∀ i t, c.threads[i]? = some t → ¬ T i → ∀ ts ∈ t.prom, ts ∉ g.pend → ∀ w, c.mem.get? ts = some w →
      mayWrite (setRes rF tid (r.op (tok D.o (D.tk n))) i) (D.handGhost g n) w.loc) :
    Erase (setRes rF tid (r.op (tok D.o (D.tk n)))) (D.handGhost g n) T c := by
  have htot := total_hand (rF := rF) (c := c) (r := r) hn E.slotsNodup h₀ hd h1
  have hkey : ((D.handGhost g n).u.map fun s => (s.key, s.id)) = g.u.map fun s => (s.key, s.id) := by
    simp only [handGhost, List.map_map]
    exact List.map_congr_left fun s _ => by simp
  refine
    { valid := by rw [htot]; exact E.valid
      slotIds := fun s hs => ?_
      acqIds := by rw [htot]; exact E.acqIds
      relAcq := by rw [htot]; exact E.relAcq
      writes := by rw [htot]; exact E.writes
      pure := E.pure
      relExists := E.relExists
      slotsNodup := by rw [hkey]; exact E.slotsNodup
      slotsDom := fun k ι => ?_
      slotsPred := fun s hs v hv => ?_
      promWf := E.promWf
      promValid := hval
      pend := E.pend
      updIds := by rw [htot]; exact E.updIds
      relSettled := E.relSettled
      claimsNodup := E.claimsNodup
      claimsAt := E.claimsAt
      claimFulf := E.claimFulf }
  · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    rw [handSlot_id]; exact E.slotIds s' hs'
  · rw [htot]
    constructor
    · rintro ⟨s, hs, hk, hi⟩
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
      exact (E.slotsDom k ι).mp ⟨s', hs', by simpa using hk, by simpa using hi⟩
    · intro h
      obtain ⟨s, hs, hk, hi⟩ := (E.slotsDom k ι).mpr h
      exact ⟨D.handSlot n s, List.mem_map.mpr ⟨s, hs, rfl⟩, by simp [hk], by simp [hi]⟩
  · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    rw [handSlot_key] at hv
    show (g.acqPred (D.handSlot n s').id).P v c.mem (D.handSlot n s').key.2 (D.handSlot n s').res
    rw [handSlot_id, handSlot_key]
    by_cases hs : D.IsDisp s'
    · have he : s' = s₀ := eq_of_nodup_map E.slotsNodup hs' h₀ (isDisp_eq hs hd)
      subst he
      rw [handSlot_res_of hs]
      have := E.slotsPred s' hs' v hv
      rw [hs.2] at this ⊢
      exact hP _ _ _ _ this
    · rw [handSlot_of_not hs]; exact E.slotsPred s' hs' v hv

/-! ## Reach: K1 and K2 -/

/-- A chain after the hand-out, of acquire ids `A'` that are `A`'s plus at
most the handed token, is a chain before it: the token's slots were reachable
through the dispenser (an update slot). -/
theorem CanAcq.hand_bwd {g : Ghost} {n : Nat} {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g.upd D.o) {A A' : Loc → PredId → Nat}
    (hA : ∀ y j, 1 ≤ A' y j → 1 ≤ A y j ∨ (y = D.o ∧ j = D.tk n)) {k : Key} {j : PredId}
    (h : CanAcq (D.handGhost g n).u g.upd A' k j) : CanAcq g.u g.upd A k j := by
  have hdisp : CanAcq g.u g.upd A s₀.key s₀.id := .upd h₀ (by rw [hd.1, hd.2]; exact hU)
  induction h with
  | @base s hs ha =>
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    simp only [handSlot_key, handSlot_id] at ha ⊢
    rcases hA _ _ ha with ha | ⟨hy, hj⟩
    · exact .base hs' ha
    · refine .step hdisp h₀ hs' ?_
      rw [hy, hj, h1]; exact Nat.le_refl _
  | @upd s hs hu =>
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    simp only [handSlot_key, handSlot_id] at hu ⊢
    exact .upd hs' hu
  | @step s s' _ hs hs' ha ih =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hs'
    simp only [handSlot_key, handSlot_id] at ha ih ⊢
    exact .step ih ht ht' (Nat.le_trans ha (handSlot_acq_le n t _ _))

/-- The bounded form (`ResModel.reach`). -/
theorem CanAcqB.hand_bwd {g : Ghost} {n : Nat} {b : Time} {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g.upd D.o) {A A' : Loc → PredId → Nat}
    (hA : ∀ y j, 1 ≤ A' y j → 1 ≤ A y j ∨ (y = D.o ∧ j = D.tk n)) {k : Key} {j : PredId}
    (h : CanAcqB (D.handGhost g n).u g.upd A' b k j) : CanAcqB g.u g.upd A b k j := by
  have h0b : s₀.key.2 ≤ b := by rw [hd.1]; exact Nat.zero_le _
  have hdisp : CanAcqB g.u g.upd A b s₀.key s₀.id := .upd h₀ h0b (by rw [hd.1, hd.2]; exact hU)
  induction h with
  | @base s hs hb ha =>
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    simp only [handSlot_key, handSlot_id] at ha hb ⊢
    rcases hA _ _ ha with ha | ⟨hy, hj⟩
    · exact .base hs' hb ha
    · refine .step hdisp h₀ hs' hb ?_
      rw [hy, hj, h1]; exact Nat.le_refl _
  | @upd s hs hb hu =>
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    simp only [handSlot_key, handSlot_id] at hu hb ⊢
    exact .upd hs' hb hu
  | @step s s' _ hs hs' hb ha ih =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hs'
    simp only [handSlot_key, handSlot_id] at ha ih hb ⊢
    exact .step ih ht ht' hb (Nat.le_trans ha (handSlot_acq_le n t _ _))

theorem tok_acq_cases (r : Res) (n : Nat) (y : Loc) (j : PredId) (h : 1 ≤ (r.op (tok D.o (D.tk n))).acq y j) :
    1 ≤ r.acq y j ∨ (y = D.o ∧ j = D.tk n) := by
  simp only [Res.op, tok] at h
  by_cases hy : y = D.o ∧ j = D.tk n
  · exact .inr hy
  · simp only [hy, ↓reduceIte, Nat.add_zero] at h; exact .inl h

/-- **K1 (unbounded, the `acqLe` conjunct)**: the receiving thread may write
nothing new after the hand-out. -/
theorem mayWrite_hand {g : Ghost} {n : Nat} {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g.upd D.o) {r : Res} {x : Loc}
    (h : mayWrite (r.op (tok D.o (D.tk n))) (D.handGhost g n) x) : mayWrite r g x := by
  rcases h with h | ⟨s, hs, hc, hq⟩
  · left; rwa [op_tok_wr] at h
  · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    right
    refine ⟨s', hs', ?_, by rwa [handSlot_wr] at hq⟩
    have := CanAcq.hand_bwd h₀ hd h1 hU (A := r.acq) (tok_acq_cases r n) hc
    simpa using this

/-- **K1 / K2 (bounded reach)**: a resource `ρ'` that is `ρ` plus at most the
handed token (`ρ' = r • tok` for the receiving thread, `ρ' = ρ` for a frame)
reaches nothing after the hand-out that `ρ` did not reach before. -/
theorem reachB_hand {g : Ghost} {n : Nat} {b : Time} {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g.upd D.o) {ρ ρ' : Res} {x : Loc}
    (hA : ∀ y j, 1 ≤ ρ'.acq y j → 1 ≤ ρ.acq y j ∨ (y = D.o ∧ j = D.tk n))
    (hw : ∀ y, 0 < (ρ'.wr y).q → 0 < (ρ.wr y).q)
    (h : reachB ρ' (D.handGhost g n) x b) : reachB ρ g x b := by
  rcases h with h | ⟨s, hs, hb, hc, hq⟩
  · exact .inl (hw x h)
  · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    right
    simp only [handSlot_key] at hb
    refine ⟨s', hs', hb, ?_, by rwa [handSlot_wr] at hq⟩
    have := CanAcqB.hand_bwd h₀ hd h1 hU hA hc
    simpa using this

/-- K1, bounded, for the receiving thread. -/
theorem reachB_hand_own {g : Ghost} {n : Nat} {b : Time} {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g.upd D.o) {r : Res} {x : Loc}
    (h : reachB (r.op (tok D.o (D.tk n))) (D.handGhost g n) x b) : reachB r g x b :=
  reachB_hand h₀ hd h1 hU (tok_acq_cases r n) (fun y h => by rwa [op_tok_wr] at h) h

/-- K2, for every frame. -/
theorem reachB_hand_frame {g : Ghost} {n : Nat} {b : Time} {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g.upd D.o) {ρ : Res} {x : Loc}
    (h : reachB ρ (D.handGhost g n) x b) : reachB ρ g x b :=
  reachB_hand h₀ hd h1 hU (fun _ _ h => .inl h) (fun _ h => h) h

/-! ## The dispenser invariant across the steps -/

/-- **Frame law**: the dispenser invariant survives a ghost step that keeps
the dispenser slot, the handed tickets, `ιD` as an update id of `o`, the
dispenser message unclaimed and `ιD`'s predicate. -/
theorem DispOK.frame {g g' : Ghost} {mem mem' : Memory} {ex : Nat → Prop} (h : D.DispOK g mem ex)
    (hs : ∀ s ∈ g.u, D.IsDisp s → s ∈ g'.u) (hH : ∀ n, D.Handed g' mem' n ↔ D.Handed g mem n)
    (hU : D.ιD ∈ g.upd D.o → D.ιD ∈ g'.upd D.o) (hcl : ¬ g.Claimed D.key → ¬ g'.Claimed D.key)
    (hP : g'.acqPred D.ιD = g.acqPred D.ιD) : D.DispOK g' mem' ex := by
  obtain ⟨⟨s, hsu, hd, hn⟩, hu, hc, hdP⟩ := h
  refine ⟨⟨s, hs s hsu hd, hd, fun n hlt => ?_⟩, hU hu, hcl hc, by rw [hP]; exact hdP⟩
  rw [hH n]; exact hn n hlt

/-- **The claim of an RMW on `x`**: after `Erase.rmw`'s ghost update for an
RMW reading `(x, tr)` (value `old`), ticket `old` was not handed out before
(`MonoX` and the read message unclaimed), and the dispenser invariant holds
with exception `old` at any extension `mem'` of the memory. -/
theorem DispOK.rmw {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    (h : D.TicketInv g c) {mem' : Memory} (hp : c.mem.Prefix mem') {tr tw : Time} {old : Val}
    (hrd : c.mem.read? D.x tr = some old) (hun : ¬ g.Claimed (D.x, tr)) {rel : Bool} {ss : List Slot} :
    ¬ D.Handed g c.mem old.toNat ∧ D.DispOK (rmwGhost g D.x tr tw rel ss) mem' (· = old.toNat) := by
  have hnot : ¬ D.Handed g c.mem old.toNat := by
    rintro ⟨tr', tw', v, hc, hr, hv⟩
    have := h.mono.ts_eq hr hrd hv
    subst this
    exact hun (List.mem_map.mpr ⟨_, hc, rfl⟩)
  have htr := lc_read?_le_last hrd
  have hH : ∀ n, D.Handed (rmwGhost g D.x tr tw rel ss) mem' n ↔ D.Handed g c.mem n ∨ n = old.toNat := by
    intro n
    constructor
    · rintro ⟨tr', tw', v, hc, hr, hv⟩
      rcases List.mem_cons.mp hc with he | hc
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨-, rfl⟩, rfl⟩ := he
        rw [hp.read? htr, hrd] at hr
        cases hr; exact .inr hv.symm
      · exact .inl ((handed_prefix hp (claims_le E) n).mp ⟨tr', tw', v, hc, hr, hv⟩)
    · rintro (hh | rfl)
      · obtain ⟨tr', tw', v, hc, hr, hv⟩ := (handed_prefix hp (claims_le E) n).mpr hh
        exact ⟨tr', tw', v, List.mem_cons_of_mem _ hc, hr, hv⟩
      · exact ⟨tr, tw, old, List.mem_cons_self .., by rw [hp.read? htr]; exact hrd, rfl⟩
  refine ⟨hnot, ?_⟩
  obtain ⟨⟨s, hsu, hd, hn⟩, hu, hc, hdP⟩ := h.disp
  have hkx : s.key ≠ (D.x, tr) := by
    rw [hd.1]; intro he; simp only [key, Prod.mk.injEq] at he; exact D.xo he.1.symm
  refine ⟨⟨s, mem_rmw_u.mpr (.inl ⟨hsu, ?_⟩), hd, fun n hlt => ?_⟩, hu, ?_, hdP⟩
  · simp [updSlot, hkx]
  · obtain ⟨h0, h1⟩ := hn n hlt
    rw [hH n]
    by_cases hno : n = old.toNat
    · subst hno
      refine ⟨fun hh => absurd rfl hh.2, fun _ => h1 fun hh => hnot hh.1⟩
    · constructor
      · rintro ⟨hh | hh, -⟩
        · exact h0 ⟨hh, id⟩
        · exact absurd hh hno
      · intro hh; exact h1 fun h' => hh ⟨.inl h'.1, hno⟩
  · rw [claimed_rmw]
    rintro (he | he)
    · simp only [key, Prod.mk.injEq] at he; exact D.xo he.1.symm
    · exact hc he

/-- **The hand-out removes the exception.** -/
theorem DispOK.handOut {g : Ghost} {mem : Memory} {n : Nat} (h : D.DispOK g mem (· = n))
    (hH : D.Handed g mem n) (hnN : n < D.N) :
    ∃ s₀ ∈ g.u, D.IsDisp s₀ ∧ s₀.res.acq D.o (D.tk n) = 1 ∧
      ((∀ s ∈ g.u, D.IsDisp s → s = s₀) → D.DispOK (D.handGhost g n) mem (fun _ => False)) := by
  obtain ⟨⟨s₀, hs₀, hd, hn⟩, hu, hc, hdP⟩ := h
  refine ⟨s₀, hs₀, hd, (hn n hnN).2 fun h' => h'.2 rfl, fun huniq => ?_⟩
  refine ⟨⟨D.handSlot n s₀, List.mem_map.mpr ⟨s₀, hs₀, rfl⟩, ⟨by simp [hd.1], by simp [hd.2]⟩,
    fun m hm => ?_⟩, hu, hc, hdP⟩
  have hHm : D.Handed (D.handGhost g n) mem m ↔ D.Handed g mem m := Iff.rfl
  rw [hHm, handSlot_res_of hd]
  by_cases hmn : m = n
  · subst hmn
    exact ⟨fun _ => by simp [dropTk], fun h' => absurd ⟨hH, not_false⟩ h'⟩
  · have hne : D.tk m ≠ D.tk n := fun h' => hmn (D.tkInj m n hm hnN h')
    have hdr : (dropTk s₀.res D.o (D.tk n)).acq D.o (D.tk m) = s₀.res.acq D.o (D.tk m) := by
      simp [dropTk, hne]
    obtain ⟨h0, h1⟩ := hn m hm
    rw [hdr]
    exact ⟨fun hh => h0 ⟨hh.1, hmn⟩, fun hh => h1 fun h' => hh ⟨h'.1, not_false⟩⟩

/-- At most one dispenser slot (`slotsNodup`). -/
theorem disp_unique {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {s₀ : Slot} (h₀ : s₀ ∈ g.u) (hd : D.IsDisp s₀) : ∀ s ∈ g.u, D.IsDisp s → s = s₀ :=
  fun _ hs hds => eq_of_nodup_map E.slotsNodup hs h₀ (isDisp_eq hds hd)

/-! ## `EraseT` under the `ldadda` step and under the take -/

/-- **Preservation of `EraseT` under a successful RMW on `x`** (the `ldadda`
step): from `EraseT` before, existing erasure after `Erase.rmw` (claim of
`(x, tr)`, value `old < N`), and `MonoX` of the memory after (the new value
is fresh: an obligation of the RMW rule), the hand-out of `tk old` gives
`EraseT` after; the thread now holds `tk old`. K1/K2 for the hand-out are
`mayWrite_hand`/`reachB_hand_own`/`reachB_hand_frame` (with the dispenser
slot given here). -/
theorem EraseT.rmwHand {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {tid : Nat}
    {r' : Res} (E : Erase rF g T c) (h : D.TicketInv g c) {tr tw : Time} {old : Val} {rel : Bool}
    {ss : List Slot} (E' : Erase (setRes rF tid r') (rmwGhost g D.x tr tw rel ss) T c')
    (hp : c.mem.Prefix c'.mem) (hn : tid < c'.threads.size) (hrd : c.mem.read? D.x tr = some old)
    (hun : ¬ g.Claimed (D.x, tr)) (hnN : old.toNat < D.N) (hmono : D.MonoX c'.mem)
    (hval : ∀ i t, c'.threads[i]? = some t → ¬ T i → ∀ ts ∈ t.prom, ts ∉ g.pend → ∀ w, c'.mem.get? ts = some w →
      mayWrite (setRes rF tid (r'.op (tok D.o (D.tk old.toNat))) i)
        (D.handGhost (rmwGhost g D.x tr tw rel ss) old.toNat) w.loc) :
    ∃ s₀ ∈ (rmwGhost g D.x tr tw rel ss).u, D.IsDisp s₀ ∧ s₀.res.acq D.o (D.tk old.toNat) = 1 ∧
      D.ιD ∈ g.upd D.o ∧
      EraseT D (setRes rF tid (r'.op (tok D.o (D.tk old.toNat))))
        (D.handGhost (rmwGhost g D.x tr tw rel ss) old.toNat) T c' := by
  obtain ⟨-, hD⟩ := DispOK.rmw (rel := rel) (ss := ss) (tw := tw) E h hp hrd hun
  have htr := lc_read?_le_last hrd
  have hH : D.Handed (rmwGhost g D.x tr tw rel ss) c'.mem old.toNat :=
    ⟨tr, tw, old, List.mem_cons_self .., by rw [hp.read? htr]; exact hrd, rfl⟩
  obtain ⟨s₀, hs₀, hd, h1, hk⟩ := DispOK.handOut hD hH hnN
  refine ⟨s₀, hs₀, hd, h1, h.disp.upd, ?_, ⟨hk (disp_unique E' hs₀ hd), hmono⟩⟩
  exact eraseHandOut E' hn hs₀ hd h1 (fun v m V r hr => hD.dPred v m V r _ hr) hval

/-- **The take keeps the ticket invariant** (the taken id is not `ιD`: `ιD`
is an update id, held by no resource). -/
theorem TicketInv.take {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r R : Res}
    {l : Loc} {ι : PredId} {ts : Time} (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hι : 1 ≤ r.acq l ι) (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (h : D.TicketInv g c) :
    D.TicketInv (takeGhost g l ι ts) c := by
  have hne : ¬ (l = D.o ∧ ι = D.ιD) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨Q, h0, -⟩ := take_total (ts := ts) E hn hT
    have := ((E.updIds D.o).2 _ h.disp.upd).2
    rw [h0] at this; simp only [Res.op] at this; omega
  obtain ⟨⟨s₀, hs₀, hd, -⟩, -, -, -⟩ := h.disp
  have hlt : D.ιD < g.acqTab.length := hd.2 ▸ E.slotIds s₀ hs₀
  refine ⟨h.disp.frame (fun s hs hds => ?_) (fun _ => Iff.rfl) id id (takeGhost_acqPred_old hlt), h.mono⟩
  have hn' : ¬ (s.key.1 = l ∧ s.id = ι) := by
    rw [hds.1, hds.2]; exact fun h' => hne ⟨h'.1.symm, h'.2.symm⟩
  exact take_mem_u hs hn'

/-- **The token-guarded take keeps `EraseT`** (`takeEraseLaw` plus
`TicketInv.take`). -/
theorem EraseT.take {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r R : Res}
    {l : Loc} {ι : PredId} {ts : Time} (E : EraseT D (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hTt : T tid) (hι : 1 ≤ r.acq l ι) (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) :
    EraseT D (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) T c :=
  ⟨Erase.take E.1 hn hTt hι hT, TicketInv.take E.1 hn hι hT E.2⟩

/-- `TakeEraseLaw` for `EraseT`. -/
def TakeEraseLawT (I : ISA) (D : Dispenser) : Prop :=
  ∀ (rF : Nat → Res) (g : Ghost) (T : Nat → Prop) (c : Config I) (tid : Nat) (r R : Res) (l : Loc)
    (ι : PredId) (ts : Time),
    EraseT D (setRes rF tid r) g T c → tid < c.threads.size → T tid → 1 ≤ r.acq l ι →
    (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u →
    EraseT D (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) T c

theorem takeEraseLawT (D : Dispenser) : TakeEraseLawT I D :=
  fun _ _ _ _ _ _ _ _ _ _ E hn hTt hι hT => Dispenser.EraseT.take E hn hTt hι hT

/-! ## The RMW's freshness obligation -/

theorem read?_get? {m : Memory} {l : Loc} {ts : Time} {v : Val} (h : m.read? l ts = some v) (h0 : ts ≠ 0) :
    ∃ w, m.get? ts = some w ∧ w.loc = l ∧ w.val = v := by
  unfold Memory.read? at h
  simp only [h0, ↓reduceIte] at h
  split at h
  · next w hw =>
    split at h
    · next hb => simp only [beq_iff_eq] at hb; cases h; exact ⟨w, hw, hb, rfl⟩
    · cases h
  · cases h

/-- **A fresh RMW write on `x` is `Fresh`** (the `MonoX` obligation of the
`ldadda` rule, append case): the RMW read `(x, tr)` (value `old`) and passed
`Memory.atomic` for `tw = |M| + 1`; the thread has no message to `x` above
`tr` (none performed, none promised: one `ldadda` per ticket); the written
value is `old + 1` without wraparound (`new.toNat = old.toNat + 1`). -/
theorem fresh_of_atomic {D : Dispenser} {mem : Memory} {tid : Nat} {tr : Time} {old new : Val}
    (hmono : D.MonoX mem) (hrd : mem.read? D.x tr = some old)
    (hat : mem.atomic D.x tid tr (mem.last + 1) = true)
    (hown : ∀ ts w, tr < ts → mem.get? ts = some w → w.loc = D.x → w.tid ≠ tid)
    (hnew : new.toNat = old.toNat + 1) : D.Fresh mem ⟨D.x, new, tid⟩ := by
  intro _ ts v hv
  show v.toNat < new.toNat
  rcases Nat.lt_or_ge tr ts with hlt | hle
  · exfalso
    have h0 : ts ≠ 0 := by omega_t
    obtain ⟨w, hw, hl, -⟩ := read?_get? hv h0
    have hts := mem.last_le_of_get?_eq_some hw
    exact hown ts w hlt hw hl (atomic_between hat hrd hlt (by omega_t) hw hl)
  · rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · have := hmono _ _ _ _ hlt hv hrd; omega
    · rw [hrd] at hv; cases hv; omega

/-- `Memory.atomic` only looks at messages up to `tw - 1`. -/
theorem atomic_prefix {m m' : Memory} (hp : m.Prefix m') {l : Loc} {tid : Nat} {tr tw : Time}
    (htr : tr < tw) (htw : tw ≤ m.last + 1) : m'.atomic l tid tr tw = m.atomic l tid tr tw := by
  unfold Memory.atomic
  rw [hp.read? (by omega_t)]
  split
  · rfl
  · apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [hp.get? (by omega_t)]

/-- **Freshness of a promise from its fulfilment** (the per-program
`FreshPromises` obligation, memory level): a promise of `new` to `x` by
thread `j`, appended at `|M_J| + 1`, that is later fulfilled (memory
`M_f ⊒ M_J`) by an atomic RMW of `j` reading `(x, tr)` (value `old`) and
writing `old + 1`, where `j` has no other message to `x` above `tr` at
promise time, is `Fresh` at promise time (given `MonoX` there). -/
theorem promise_fresh_of_fulfil {D : Dispenser} {mJ mf : Memory} {j : Nat} {tr : Time} {old new : Val}
    (hp : mJ.Prefix mf) (hmono : D.MonoX mJ) (htr : tr < mJ.last + 1)
    (hrd : mf.read? D.x tr = some old) (hat : mf.atomic D.x j tr (mJ.last + 1) = true)
    (hown : ∀ ts w, tr < ts → mJ.get? ts = some w → w.loc = D.x → w.tid ≠ j)
    (hnew : new.toNat = old.toNat + 1) : D.Fresh mJ ⟨D.x, new, j⟩ := by
  have htr' : tr ≤ mJ.last := by omega_t
  rw [hp.read? htr'] at hrd
  rw [atomic_prefix hp htr (Nat.le_refl _)] at hat
  exact fresh_of_atomic hmono hrd hat hown hnew

end Dispenser

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.Dispenser.eraseHandOut
#print axioms Kraken.Promising.SLR.Dispenser.mayWrite_hand
#print axioms Kraken.Promising.SLR.Dispenser.reachB_hand_own
#print axioms Kraken.Promising.SLR.Dispenser.reachB_hand_frame
#print axioms Kraken.Promising.SLR.Dispenser.EraseT.rmwHand
#print axioms Kraken.Promising.SLR.Dispenser.takeEraseLawT
#print axioms Kraken.Promising.SLR.Dispenser.fresh_of_atomic
#print axioms Kraken.Promising.SLR.Dispenser.promise_fresh_of_fulfil
#print axioms Kraken.Promising.SLR.Dispenser.ticketInv_extLaws
