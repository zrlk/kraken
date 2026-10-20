import WeakCore.TermPlant
import WeakCore.TermCut
import WeakCore.TermSys

/-! # TermOverCrDefs: the definitions of the `SysInvN` clauses `overCrG` and `promAboveG`

Split from `TermOverCr` so that `TermMainDefs` can import them (`TermOverCr` sits above
`TermMainDefs`, via `TermPlantOpG`).
-/

namespace TermOverCr
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (guard, label-wide) `PlantOpG`'s window conditions (A)+(B) at bound `tw`: every message at
`l` up to `tw` is an own promise or seen (coherence), and every footprint promise at `l` lies above
`tw`. -/
def WinGL (E : TEnv) (s : St) (l : AllocLabel) (tw : Ts) : Prop :=
  (∀ t m, s.mem[t]? = some m → m.loc.label = l → t ≤ tw → t ∈ s.promises ∨ t ≤ s.vs.coh m.loc) ∧
  ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc.label = l → tw < t

/-- (guard, F3) **The window conditions at the unit `⟨l, o⟩`**: (A) and (B) restricted to the
messages at the unit itself. -/
def WinG (E : TEnv) (s : St) (l : AllocLabel) (o : Nat) (tw : Ts) : Prop :=
  (∀ t m, s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw → t ∈ s.promises ∨ t ≤ s.vs.coh m.loc) ∧
  ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → tw < t

/-- The label-wide window conditions give the per-unit ones. -/
theorem winG_of_L {E : TEnv} {s : St} {l : AllocLabel} {tw : Ts} (h : WinGL E s l tw) (o : Nat) :
    WinG E s l o tw :=
  ⟨fun t m hm hl ht => h.1 t m hm (by rw [hl]) ht, fun t m ht hm hl => h.2 t m ht hm (by rw [hl])⟩

/-- The window conditions are downward closed in the bound. -/
theorem winG_mono {E : TEnv} {s : St} {l : AllocLabel} {o : Nat} {tw wB : Ts} (h : WinG E s l o wB)
    (hle : tw ≤ wB) : WinG E s l o tw :=
  ⟨fun t m hm hl ht => h.1 t m hm hl (Nat.le_trans ht hle),
    fun t m ht hm hl => Nat.lt_of_le_of_lt hle (h.2 t m ht hm hl)⟩

/-- The label-wide window conditions are downward closed in the bound. -/
theorem winGL_mono {E : TEnv} {s : St} {l : AllocLabel} {tw wB : Ts} (h : WinGL E s l wB) (hle : tw ≤ wB) :
    WinGL E s l tw :=
  ⟨fun t m hm hl ht => h.1 t m hm hl (Nat.le_trans ht hle),
    fun t m ht hm hl => Nat.lt_of_le_of_lt hle (h.2 t m ht hm hl)⟩

/-- (PredCov, (iii)) **A credited item, predicted-unit form**: `TermPlant.CrItem`, except that at
a `K` word of a predicted unit (`PredU`) whose lowest own promise is the unit's first write, the
pinned word may be that first write's own word (its predecessor is the allocation placeholder). -/
def CrItemQ (E : TEnv) (s : St) (cr : Ts → Res) (l : AllocLabel) (c : Cell)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ mh usS, s.mem[x.1]? = some mh ∧ mh.loc.label = l ∧ TermPlant.LowOwn s mh.loc x.1 ∧
    ¬ WordUnit E mh.loc ∧ AtOff c.ty x.2.1 x.2.2.1 ∧ Solid x.2.2.1 ∧ accs x.2.2.1 = some usS ∧
    x.2.1 ≤ mh.loc.offset ∧ mh.loc.offset < x.2.1 + nWords usS ∧
    x.2.2.2.1.length = nWords usS ∧ ValOfR E x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧ x.2.2.2.2.1 ≤ cr x.1 ∧
    ∀ i o w tw', x.2.2.2.2.2 i = true → InAcc usS i o → x.2.2.2.1[o]? = some w →
      TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ tw' → PredAt s.mem ⟨l, x.2.1 + o⟩ tw' w ∨
        (PredU E ⟨l, x.2.1 + o⟩ ∧ FirstW s.mem ⟨l, x.2.1 + o⟩ tw' ∧ ∃ m, s.mem[tw']? = some m ∧ mw m = w)

/-- A plain credited item is one. -/
theorem crItemQ_of {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (h : TermPlant.CrItem E s cr l c x) :
    CrItemQ E s cr l c x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hp⟩ := h
  exact ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    fun i o w tw' hk hi hw hl => .inl (hp i o w tw' hk hi hw hl)⟩

/-- (PredCov) The units the credited cover answers for: initialised at the real count, or
predicted (`PredU`, pinned at the first write). -/
abbrev CovU (E : TEnv) (c : Cell) (l : AllocLabel) (o : Nat) : Prop := InitRr E c l o ∨ PredU E ⟨l, o⟩

/-- The credited cover of the own frontier cell `l` (type `c.ty`) by the item list `Gs`, at the
units whose lowest own promise meets the guard `G` (at the unit). -/
abbrev OverCrL (E : TEnv) (s : St) (cr : Ts → Res) (l : AllocLabel) (c : Cell) (G : Nat → Ts → Prop)
    (Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) : Prop :=
    (Gs.map (·.1)).Nodup ∧ (∀ x ∈ Gs, CrItemQ E s cr l c x) ∧
    (∀ o tw, CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G o tw →
      TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∧
    (∀ x ∈ Gs, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0) ∧
    ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr t ≠ .zero → t ∈ Gs.map (·.1)

/-- (β′) **Every item's holder is the lowest own promise of its piece**: a promise is fulfilled
(then the item is re-keyed, 2a) or new promises land above memory.  A second store's drop
item at the piece is credited at this holder (`TermOverCrW.crItem_merge`). -/
def HolderLow (s : St) (l : AllocLabel) (Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) : Prop :=
  ∀ x ∈ Gs, ∀ usS, accs x.2.2.1 = some usS → ∀ t m, t ∈ s.promises → s.mem[t]? = some m →
    m.loc.label = l → x.2.1 ≤ m.loc.offset → m.loc.offset < x.2.1 + nWords usS → x.1 ≤ t

/-- The credited cover, guarded by the window conditions, with its item list hidden. -/
def OverCrE (E : TEnv) (s : St) (cr : Ts → Res) (l : AllocLabel) (c : Cell) : Prop :=
  ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)), OverCrL E s cr l c (WinG E s l) Gs ∧
    HolderLow s l Gs

/-- (system clause) **Every thread's own frontier cells carry the credited cover**, at
every cut. -/
def OverCrG (Eg : GEnv) (c : Cfg) (cr : Nat → Ts → Res) : Prop :=
  ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th → ∀ l cl, (Cut Eg i S).sto l = some cl →
    cl.owner = some i → Eg.pfr l ≠ none → OverCrE (Cut Eg i S) (stOf c.mem c.pairs th) (cr i) l cl


/-- **Every thread's outstanding promises are above its coherence.** -/
def PromAboveG (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh), c.ths[j]? = some th → PromAbove (stOf c.mem c.pairs th)

/-! ## (β′) holder lowness along steps -/

/-- Along a step keeping the holders' messages, whose new promises lie above every holder. -/
theorem holderLow_tr {s s' : St} {l : AllocLabel} {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hmem : ∀ t m, t ∈ s'.promises → t ∈ s.promises → s'.mem[t]? = some m → s.mem[t]? = some m)
    (hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → ∀ x ∈ Gs, x.1 ≤ t)
    (h : HolderLow s l Gs) : HolderLow s' l Gs := by
  intro x hx usS hus t m ht hm hl h1 h2
  by_cases hin : t ∈ s.promises
  · exact h x hx usS hus t m hin (hmem t m ht hin hm) hl h1 h2
  · exact hnew t ht hin x hx

theorem holderLow_append {s : St} {l : AllocLabel} {A B : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hA : HolderLow s l A) (hB : HolderLow s l B) : HolderLow s l (A ++ B) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hA x h
  · exact hB x h

theorem holderLow_sublist {s : St} {l : AllocLabel} {A B : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hAB : A.Sublist B) (hB : HolderLow s l B) : HolderLow s l A :=
  fun x hx => hB x (hAB.subset hx)

/-- An in-place upgrade (same holder, piece and type) keeps holder lowness. -/
theorem holderLow_map {s : St} {l : AllocLabel} {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (f : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (hf : ∀ x ∈ Gs, (f x).1 = x.1 ∧ (f x).2.1 = x.2.1 ∧ (f x).2.2.1 = x.2.2.1)
    (h : HolderLow s l Gs) : HolderLow s l (Gs.map f) := by
  intro y hy usS hus t m ht hm hl h1 h2
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  obtain ⟨e1, e2, e3⟩ := hf x hx
  rw [e3] at hus
  rw [e2] at h1 h2
  rw [e1]
  exact h x hx usS hus t m ht hm hl h1 h2

end TermOverCr

