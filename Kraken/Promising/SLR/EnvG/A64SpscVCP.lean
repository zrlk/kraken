/-
**Part 3: the producer's invariants and
VCs** on `EnvGTU isa Arch.armv8` (the cumulative take route).

**Producer** (round `k = 1, 2, 3`: `W3 = k`, `X4 = k - 1`, `X7` the slot
`slot k` written in the round; `nv k` the value `k`):
- `PR k` (at `prod_loop`): all of `T` (every write at or below `coh T`);
  spin facts at `H` with every message up to the last one read `K` of low
  word `≤ 3`; round 1: all of `B0`, `B1`, `GA`, and every `head` message up
  to `K` is `0`; round 2: all of `B1`, the own `tail = 1` message, and
  `B0Back` (all of `B0` and `GB` already, or every `head` message up to `K`
  is `0`); round 3: the own `tail = 2` message and `B0Back`.
- `PX k` (after the spin's exit): the round's slot is held; round 3 has
  collected `B0` and `GB` (from the `head = 1` slot, read or **skipped**:
  `scanH`).
- `PD k` (after the data store): all of the slot with maximal write `k` at
  or below `vwOld`.
- `vcP_spin` (`LDAR X5, [X1]`), `vcP_storeB` (`STR W3, [X7]`), and
  **`vcP_storeT`** (`STLR X4, [X2]`, the planned release of `tail := k`).
  The release of `tail := 2` (`tail := 3`) needs, at every anchor memory, the
  writer's own `tail = 1` (`tail = 2`) message below the fresh timestamp
  (`psiT`'s `Prev`): it is in the producer's snapshot (`MsgAt`, recorded by
  the previous release, `read?_of_writeSnap`) and hence in every anchor
  (`prev_of_snap`).
-/
import Kraken.Promising.SLR.EnvG.A64SpscRead
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The environments -/

/-- The producer's environment. -/
abbrev EP (P : SP) (tid : Nat) : SharedEnv := EnvGTU isa Arch.armv8 tid (prodPlan P)

/-- The consumer's environment. -/
abbrev EC (P : SP) (tid : Nat) : SharedEnv := EnvGTU isa Arch.armv8 tid (consPlan P)

/-! ## Ownership facts -/

-- `Hold` … `full_after` are the ISA-neutral `SpscCommon` facts.
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.Full ↦ Kraken.Promising.SLR.EnvG.SpscA.Full,
  Kraken.Promising.SLR.EnvG.SpscCommon.KeepsFull ↦ Kraken.Promising.SLR.EnvG.SpscA.KeepsFull,
  Kraken.Promising.SLR.EnvG.SpscCommon.Hold ↦ Kraken.Promising.SLR.EnvG.SpscA.Hold,
  Kraken.Promising.SLR.EnvG.SpscCommon.Hold.mono ↦ Kraken.Promising.SLR.EnvG.SpscA.Hold.mono,
  Kraken.Promising.SLR.EnvG.SpscCommon.Hold.keep ↦ Kraken.Promising.SLR.EnvG.SpscA.Hold.keep,
  Kraken.Promising.SLR.EnvG.SpscCommon.Full.mono ↦ Kraken.Promising.SLR.EnvG.SpscA.Full.mono,
  Kraken.Promising.SLR.EnvG.SpscCommon.Full.keep ↦ Kraken.Promising.SLR.EnvG.SpscA.Full.keep,
  Kraken.Promising.SLR.EnvG.SpscCommon.Full.hold ↦ Kraken.Promising.SLR.EnvG.SpscA.Full.hold,
  Kraken.Promising.SLR.EnvG.SpscCommon.q_keep ↦ Kraken.Promising.SLR.EnvG.SpscA.q_keep,
  Kraken.Promising.SLR.EnvG.SpscCommon.wr_after_ne ↦ Kraken.Promising.SLR.EnvG.SpscA.wr_after_ne]

hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.wr_only_mem ↦ Kraken.Promising.SLR.EnvG.SpscA.wr_only_mem,
  Kraken.Promising.SLR.EnvG.SpscCommon.min_mono ↦ Kraken.Promising.SLR.EnvG.SpscA.min_mono]

hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.Full ↦ Kraken.Promising.SLR.EnvG.SpscA.Full,
  Kraken.Promising.SLR.EnvG.SpscCommon.keepsFull_store ↦ Kraken.Promising.SLR.EnvG.SpscA.keepsFull_store,
  Kraken.Promising.SLR.EnvG.SpscCommon.full_after ↦ Kraken.Promising.SLR.EnvG.SpscA.full_after]

/-! ## The plans at the producer's stores -/

section Plans

variable {P : SP}

theorem prod_whole (l : Loc) (v : Val) : (prodPlan P).Whole l v :=
  Plan.Whole.of_entries (fun e he => by
    simp only [prodPlan, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl) l v

theorem prod_rel_ne {x : Loc} (hx : x ≠ P.T) (v : Val) : (prodPlan P).rel x v = false := by
  simp [prodPlan, Plan.rel, Plan.find?, Ne.symm hx]

theorem prod_gives_ne {x : Loc} (hx : x ≠ P.T) (v : Val) : (prodPlan P).gives x v = [] := by
  simp [prodPlan, Plan.gives, Plan.find?, Ne.symm hx]

theorem prod_rel_T1 : (prodPlan P).rel P.T 1#128 = true := by simp [prodPlan, Plan.rel, Plan.find?]
theorem prod_gives_T1 : (prodPlan P).gives P.T 1#128 = [P.B0, GA] := by simp [prodPlan, Plan.gives, Plan.find?]
theorem prod_rel_T2 : (prodPlan P).rel P.T 2#128 = true := by simp [prodPlan, Plan.rel, Plan.find?]
theorem prod_gives_T2 : (prodPlan P).gives P.T 2#128 = [P.B1] := by simp [prodPlan, Plan.gives, Plan.find?]
theorem prod_rel_T3 : (prodPlan P).rel P.T 3#128 = true := by simp [prodPlan, Plan.rel, Plan.find?]
theorem prod_gives_T3 : (prodPlan P).gives P.T 3#128 = [P.B0, GB] := by simp [prodPlan, Plan.gives, Plan.find?]

end Plans

/-- The release predicates over a store's anchor. -/
theorem rel_store {A : Arch} {pl : Plan} {tid : Nat} {σ σ' : State isa} {k : StoreKind}
    {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (hs : (EnvGTU isa A tid pl).step (.store k xcl a n v) σ b σ') : σ'.g.rel = σ.g.rel := by
  obtain ⟨c, tw, hanc, -⟩ := step_storeFactsTU hs
  exact hanc.rel

/-- **A memory fact survives a store** (the snapshot only grows). -/
theorem msg_store {A : Arch} {pl : Plan} {tid : Nat} {σ σ' : State isa} {k : StoreKind}
    {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (hs : (EnvGTU isa A tid pl).step (.store k xcl a n v) σ b σ') {l : Loc} {t : Time} {u : Val}
    (hr : σ.snap.mem.read? l t = some u) : σ'.snap.mem.read? l t = some u := by
  obtain ⟨c, tw, hanc, hws, -⟩ := step_storeFactsTU hs
  exact writeSnap_read? hws (hanc.snap.read? hr)

/-- The snapshot after a store extends the one before. -/
theorem snapLe_store {A : Arch} {pl : Plan} {tid : Nat} {σ σ' : State isa} {k : StoreKind}
    {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (hs : (EnvGTU isa A tid pl).step (.store k xcl a n v) σ b σ') : σ.snap.mem.Prefix σ'.snap.mem := by
  obtain ⟨c, tw, hanc, hws, -⟩ := step_storeFactsTU hs
  have h1 : σ.snap.mem.Prefix c.mem := ⟨hanc.snap.init, hanc.snap.msgs⟩
  have h2 : c.mem.Prefix σ'.snap.mem := by
    rcases hws.mem with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]; exact ⟨rfl, List.prefix_refl _⟩
    · rw [hm]; exact Memory.Prefix.append _ _
  exact ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩

/-! ## The producer's values -/

/-- The value `k` (data and counters). -/
abbrev nv (k : Nat) : Val := BitVec.ofNat 128 k

/-- The slot written in producer round `k`. -/
def slot (P : SP) (k : Nat) : Loc := if k = 2 then P.B1 else P.B0

theorem slot_ne_T {P : SP} (hL : SpscLocs P) (k : Nat) : slot P k ≠ P.T := by
  unfold slot; split
  · exact hL.b1_t
  · exact hL.b0_t

theorem slot_ne_H {P : SP} (hL : SpscLocs P) (k : Nat) : slot P k ≠ P.H := by
  unfold slot; split
  · exact hL.b1_h
  · exact hL.b0_h

theorem relS_slot {P : SP} (hL : SpscLocs P) (k : Nat) : relS P (slot P k) = Pred.emp :=
  relS_other (slot_ne_T hL k) (slot_ne_H hL k)

/-- A message of `l` with low word `k` in the snapshot. -/
def MsgAt (σ : State isa) (l : Loc) (k : BitVec 64) : Prop := ∃ t u, σ.snap.mem.read? l t = some u ∧ lo u = k

theorem MsgAt.fence {σ σ' : State isa} {l : Loc} {k : BitVec 64} (h : MsgAt σ l k) (hf : FenceLe σ σ') :
    MsgAt σ' l k := by unfold MsgAt; rw [hf.snap]; exact h

theorem MsgAt.load {tid : Nat} {σ σ' : State isa} {l : Loc} {k : BitVec 64} (h : MsgAt σ l k)
    (hk : LoadKeepU tid σ σ') : MsgAt σ' l k :=
  h.elim fun t ⟨u, hr, hu⟩ => ⟨t, u, hk.snap.read? hr, hu⟩

/-! ## The producer's invariants -/

/-- `B0` and `GB` are back with the producer. -/
def GotB0 (P : SP) (σ : State isa) : Prop := Hold P.B0 σ.vs.vwNew σ.r ∧ (σ.r.wr GB).q = 1

/-- **The `head` spin facts** of the producer, with every message up to the
last one read of low word `≤ 3`, and the round's knowledge `Z` about them. -/
def SpinH (P : SP) (Z : Time → State isa → Prop) (σ : State isa) : Prop :=
  ∃ K, SpinU P.H (psiH P) K σ ∧ UpTo σ.snap.mem P.H K (· ≤ 3) ∧ Z K σ

/-- Every `head` message up to `K` is `0`. -/
def HZero (P : SP) (K : Time) (σ : State isa) : Prop := UpTo σ.snap.mem P.H K (· = 0)

/-- `B0` is back, or every `head` message up to `K` is `0`. -/
def B0Back (P : SP) (K : Time) (σ : State isa) : Prop := GotB0 P σ ∨ HZero P K σ

/-- **At `prod_loop`** of round `k`. -/
def PR (P : SP) (k : Nat) (σ : State isa) : Prop :=
  σ.g.rel = relS P ∧ Hold P.T (σ.vs.getCoh P.T) σ.r ∧
    (k = 1 → Hold P.B0 σ.vs.vwNew σ.r ∧ Hold P.B1 σ.vs.vwNew σ.r ∧ (σ.r.wr GA).q = 1 ∧ SpinH P (HZero P) σ) ∧
    (k = 2 → Hold P.B1 σ.vs.vwNew σ.r ∧ MsgAt σ P.T 1 ∧ SpinH P (B0Back P) σ) ∧
    (k = 3 → MsgAt σ P.T 2 ∧ SpinH P (B0Back P) σ)

/-- **After the spin's exit** in round `k`. -/
def PX (P : SP) (k : Nat) (σ : State isa) : Prop :=
  σ.g.rel = relS P ∧ Hold P.T (σ.vs.getCoh P.T) σ.r ∧ Hold (slot P k) σ.vs.vwNew σ.r ∧
    (k = 1 → Hold P.B1 σ.vs.vwNew σ.r ∧ (σ.r.wr GA).q = 1 ∧ SpinH P (HZero P) σ) ∧
    (k = 2 → MsgAt σ P.T 1 ∧ SpinH P (B0Back P) σ) ∧
    (k = 3 → (σ.r.wr GB).q = 1 ∧ MsgAt σ P.T 2)

/-- **After the data store** in round `k`. -/
def PD (P : SP) (k : Nat) (σ : State isa) : Prop :=
  σ.g.rel = relS P ∧ Hold P.T (σ.vs.getCoh P.T) σ.r ∧ Full (slot P k) (nv k) σ.vs.vwOld σ.r ∧
    (k = 1 → Hold P.B1 σ.vs.vwNew σ.r ∧ (σ.r.wr GA).q = 1 ∧ SpinH P (HZero P) σ) ∧
    (k = 2 → MsgAt σ P.T 1 ∧ SpinH P (B0Back P) σ) ∧
    (k = 3 → (σ.r.wr GB).q = 1 ∧ MsgAt σ P.T 2)

/-! ### Fences -/

section Fence

variable {P : SP} {k : Nat} {σ σ' : State isa}

theorem SpinH.fence {Z : Time → State isa → Prop} (hZ : ∀ K, Z K σ → Z K σ') (h : SpinH P Z σ)
    (hf : FenceLe σ σ') : SpinH P Z σ' :=
  h.elim fun K ⟨hs, hu, hz⟩ => ⟨K, hs.fence hf, by rw [hf.snap]; exact hu, hZ K hz⟩

theorem HZero.fence {K : Time} (h : HZero P K σ) (hf : FenceLe σ σ') : HZero P K σ' := by
  unfold HZero; rw [hf.snap]; exact h

theorem GotB0.fence (h : GotB0 P σ) (hf : FenceLe σ σ') : GotB0 P σ' :=
  ⟨by rw [hf.r]; exact h.1.mono hf.vwNew, by rw [hf.r]; exact h.2⟩

theorem B0Back.fence {K : Time} (h : B0Back P K σ) (hf : FenceLe σ σ') : B0Back P K σ' :=
  h.imp (·.fence hf) (·.fence hf)

theorem PR.fence (h : PR P k σ) (hf : FenceLe σ σ') : PR P k σ' := by
  obtain ⟨hrel, hT, h1, h2, h3⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  refine ⟨by rw [hf.g]; exact hrel, hT.keep hk (Nat.le_of_eq (hf.getCoh _).symm), fun e => ?_, fun e => ?_,
    fun e => ?_⟩
  · obtain ⟨a, b, c, d⟩ := h1 e
    exact ⟨a.keep hk hf.vwNew, b.keep hk hf.vwNew, q_keep c hk, d.fence (fun _ h => h.fence hf) hf⟩
  · obtain ⟨a, b, d⟩ := h2 e
    exact ⟨a.keep hk hf.vwNew, b.fence hf, d.fence (fun _ h => h.fence hf) hf⟩
  · obtain ⟨b, d⟩ := h3 e
    exact ⟨b.fence hf, d.fence (fun _ h => h.fence hf) hf⟩

theorem PX.fence (h : PX P k σ) (hf : FenceLe σ σ') : PX P k σ' := by
  obtain ⟨hrel, hT, hs, h1, h2, h3⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  refine ⟨by rw [hf.g]; exact hrel, hT.keep hk (Nat.le_of_eq (hf.getCoh _).symm), hs.keep hk hf.vwNew,
    fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨b, c, d⟩ := h1 e
    exact ⟨b.keep hk hf.vwNew, q_keep c hk, d.fence (fun _ h => h.fence hf) hf⟩
  · obtain ⟨b, d⟩ := h2 e
    exact ⟨b.fence hf, d.fence (fun _ h => h.fence hf) hf⟩
  · obtain ⟨b, d⟩ := h3 e
    exact ⟨q_keep b hk, d.fence hf⟩

theorem PD.fence (h : PD P k σ) (hf : FenceLe σ σ') : PD P k σ' := by
  obtain ⟨hrel, hT, hs, h1, h2, h3⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  refine ⟨by rw [hf.g]; exact hrel, hT.keep hk (Nat.le_of_eq (hf.getCoh _).symm),
    hs.keep hk (Nat.le_of_eq hf.vwOld.symm), fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨b, c, d⟩ := h1 e
    exact ⟨b.keep hk hf.vwNew, q_keep c hk, d.fence (fun _ h => h.fence hf) hf⟩
  · obtain ⟨b, d⟩ := h2 e
    exact ⟨b.fence hf, d.fence (fun _ h => h.fence hf) hf⟩
  · obtain ⟨b, d⟩ := h3 e
    exact ⟨q_keep b hk, d.fence hf⟩

end Fence

/-! ## The `tail` release (the first milestone) -/

/-- **VC `STLR X4, [X2]`** (the `tail` release of round `k`, value `k`):
permitted (planned, `psiT` impure, `T` kept, and the uniform obligation:
the slot written and the token satisfy `psiT`; for `k = 2, 3` the own
`tail = k - 1` message is below the fresh timestamp in every anchor
memory), and gives `PR (k + 1)` (rounds 1, 2) and all of `T`. -/
theorem vcP_storeT {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ : State isa}
    (h : PD P k σ) :
    (EP P tid).ok (.store .rel false P.t 8 (nv k)) σ ∧
      ∀ b (σ' : State isa), (EP P tid).step (.store .rel false P.t 8 (nv k)) σ b σ' →
        (k = 1 → PR P 2 σ') ∧ (k = 2 → PR P 3 σ') ∧ (σ'.r.wr P.T).q = 1 := by
  obtain ⟨hrel, ⟨hqT, hmT⟩, hS, h1, h2, h3⟩ := h
  have hrl : (prodPlan P).rel P.T (nv k) = true := by
    rcases hk3 with rfl | rfl | rfl
    · exact prod_rel_T1
    · exact prod_rel_T2
    · exact prod_rel_T3
  have hwh := prod_whole (P := P) P.T (nv k)
  have hTg : P.T ∉ (prodPlan P).gives P.T (nv k) := (prodPlan_valid hL).not_mem_gives _ _
  refine ⟨⟨rfl, by show 0 < (σ.r.wr P.T).q; rw [hqT]; decide, fun hr => absurd (hr.symm.trans hrl) Bool.false_ne_true,
    fun _ => ⟨effRel_rel _ _, by show ¬ Pred.Pure (σ.g.rel P.T) _; rw [hrel, relS_T]; exact psiT_impure P _, hTg,
      ?_⟩⟩, ?_⟩
  · intro c g hanc hwb
    have hlt := hwb.rel rfl
    show (σ.g.rel P.T).P _ _ _ _
    rw [hrel, relS_T, Plan.give_of_whole _ hwh]
    obtain ⟨hqS, ts, hX, hm, hts⟩ := hS
    have hV : ts ≤ c.mem.last + 1 := by simp only [Time, View] at *; omega
    rcases hk3 with rfl | rfl | rfl
    · obtain ⟨-, hGA, -⟩ := h1 rfl
      rw [show nv 1 = 1#128 from rfl, prod_gives_T1]
      have e1 : P.B0 ∈ [P.B0, GA] := by simp
      have e2 : GA ∈ [P.B0, GA] := by simp
      refine .inr (.inl ⟨rfl, ⟨by rw [wr_only_mem e1]; exact hqS, ts, by rw [wr_only_mem e1]; exact hX,
        fun p hp => hm p (by rw [wr_only_mem e1] at hp; exact hp), hV⟩, by rw [wr_only_mem e2]; exact hGA⟩)
    · obtain ⟨hM, -⟩ := h2 rfl
      rw [show nv 2 = 2#128 from rfl, prod_gives_T2]
      have e1 : P.B1 ∈ [P.B1] := by simp
      refine .inr (.inr (.inl ⟨rfl, ⟨by rw [wr_only_mem e1]; exact hqS, ts, by rw [wr_only_mem e1]; exact hX,
        fun p hp => hm p (by rw [wr_only_mem e1] at hp; exact hp), hV⟩, prev_of_snap hanc hM _⟩))
    · obtain ⟨hGB, hM⟩ := h3 rfl
      rw [show nv 3 = 3#128 from rfl, prod_gives_T3]
      have e1 : P.B0 ∈ [P.B0, GB] := by simp
      have e3 : GB ∈ [P.B0, GB] := by simp
      refine .inr (.inr (.inr ⟨rfl, ⟨by rw [wr_only_mem e1]; exact hqS, ts, by rw [wr_only_mem e1]; exact hX,
        fun p hp => hm p (by rw [wr_only_mem e1] at hp; exact hp), hV⟩, by rw [wr_only_mem e3]; exact hGB,
        prev_of_snap hanc hM _⟩))
  intro b σ' hs
  have hrel' := rel_store hs
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨Pc, -, hr⟩, -⟩ := step_storeFactsTU hs
  have hTfull : Full P.T (nv k) (σ'.vs.getCoh P.T) σ'.r := by
    rw [hr]
    exact full_after hwh hTg hqT (fun p hp => Nat.lt_of_le_of_lt (hmT p hp) hwb.coh) hwv.coh
  have hkf : ∀ x, x ≠ P.T → x ∉ (prodPlan P).gives P.T (nv k) → (σ.r.wr x).q = 1 →
      (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (σ.r.wr x).X p :=
    fun x hx hg hq => by rw [hr]; exact keepsFull_store hx hwh hg hq
  have hvw := hwv.mono.vwNew
  have hpre := snapLe_store hs
  have hmsg : MsgAt σ' P.T (lo (nv k)) :=
    ⟨tw, nv k, read?_of_writeSnap hws (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hwb.vwNew)), rfl⟩
  have hgH : P.H ∉ (prodPlan P).gives P.T (nv k) := by
    rcases hk3 with rfl | rfl | rfl
    · rw [show nv 1 = 1#128 from rfl, prod_gives_T1]; simp [hL.b0_h.symm, ne_ga (show (8 : Nat) ≠ 5 by decide)]
    · rw [show nv 2 = 2#128 from rfl, prod_gives_T2]; simp [hL.b1_h.symm]
    · rw [show nv 3 = 3#128 from rfl, prod_gives_T3]; simp [hL.b0_h.symm, ne_gb (show (8 : Nat) ≠ 5 by decide)]
  -- the spin facts and the `head` knowledge survive the store
  have hspin : ∀ {Z Z' : Time → State isa → Prop},
      (∀ K, SpinU P.H (psiH P) K σ → Z K σ → Z' K σ') → SpinH P Z σ → SpinH P Z' σ' := by
    intro Z Z' hZ ⟨K, hsp, hu, hz⟩
    exact ⟨K, hsp.store_other hs hL.h_t hwh hgH, hu.prefix hpre (hsp.msg.elim fun _ hr => read?_le_last hr),
      hZ K hsp hz⟩
  have hHZ : ∀ K, SpinU P.H (psiH P) K σ → HZero P K σ → HZero P K σ' := fun K hsp hz =>
    UpTo.prefix hz hpre (hsp.msg.elim fun _ hr => read?_le_last hr)
  refine ⟨fun e => ?_, fun e => ?_, hTfull.1⟩
  · subst e
    obtain ⟨hB1, hGA, hsp⟩ := h1 rfl
    have hg : P.B1 ∉ (prodPlan P).gives P.T (nv 1) := by
      rw [show nv 1 = 1#128 from rfl, prod_gives_T1]
      simp [Ne.symm (b0_b1 P), ne_ga (show (4 : Nat) ≠ 5 by decide)]
    have hB1' := hkf P.B1 hL.b1_t hg hB1.1
    refine ⟨by rw [hrel']; exact hrel, hTfull.hold, fun e => absurd e (by decide),
      fun _ => ⟨⟨hB1'.1, fun p hp => Nat.le_trans (hB1.2 p ((hB1'.2 p).mp hp)) hvw⟩, hmsg,
        hspin (fun K hs' hz => .inr (hHZ K hs' hz)) hsp⟩,
      fun e => absurd e (by decide)⟩
  · subst e
    obtain ⟨-, hsp⟩ := h2 rfl
    have hgB0 : P.B0 ∉ (prodPlan P).gives P.T (nv 2) := by
      rw [show nv 2 = 2#128 from rfl, prod_gives_T2]; simp [b0_b1 P]
    have hgGB : GB ∉ (prodPlan P).gives P.T (nv 2) := by
      rw [show nv 2 = 2#128 from rfl, prod_gives_T2]; simp [(ne_gb (show (4 : Nat) ≠ 5 by decide)).symm]
    refine ⟨by rw [hrel']; exact hrel, hTfull.hold, fun e => absurd e (by decide), fun e => absurd e (by decide),
      fun _ => ⟨hmsg, hspin (fun K hs' hz => ?_) hsp⟩⟩
    rcases hz with ⟨hB0, hGB⟩ | hz
    · have hB0' := hkf P.B0 hL.b0_t hgB0 hB0.1
      exact .inl ⟨⟨hB0'.1, fun p hp => Nat.le_trans (hB0.2 p ((hB0'.2 p).mp hp)) hvw⟩,
        (hkf GB (ne_gb (by decide)).symm hgGB hGB).1⟩
    · exact .inr (hHZ K hs' hz)

/-! ## The `head` spin -/

/-- `psiH`'s values: `0` to `3`. -/
theorem psiH_val {P : SP} {v : Val} {m : Memory} {V : View} {R : Res} (h : (psiH P).P v m V R) : lo v ≤ 3 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ <;> rw [h] <;> decide

theorem GotB0.load {P : SP} {tid : Nat} {σ σ' : State isa} (h : GotB0 P σ) (hk : LoadKeepU tid σ σ') :
    GotB0 P σ' :=
  ⟨h.1.keep hk.full hk.vs.vwNew, q_keep h.2 hk.full⟩

/-- **The scan of a `head` spin read** (`LDAR X5, [X1]`): the read `tr`
moves the spin facts; every message up to `tr` is `≤ 3`; and if every
message up to `K` was `0`, then either every message up to `tr` is `0`, or
some message in `(K, tr]` (read or **skipped**) is `1`, whose slot gave
`B0` and `GB` back (and the producer held no `B0` before). -/
theorem scanH {P : SP} (hL : SpscLocs P) {tid : Nat} {K : Time} {σ σ' : State isa} {v : Val}
    (hrel : σ.g.rel = relS P) (hsp : SpinU P.H (psiH P) K σ) (hup : UpTo σ.snap.mem P.H K (· ≤ 3))
    (hs : (EP P tid).step (.load .acq false P.h 8) σ v σ') :
    ∃ tr, SpinU P.H (psiH P) tr σ' ∧ σ'.snap.mem.read? P.H tr = some v ∧ UpTo σ'.snap.mem P.H tr (· ≤ 3) ∧
      (HZero P K σ → HZero P tr σ' ∨ ((σ.r.wr P.B0).q = 0 ∧ GotB0 P σ')) := by
  have hk := loadKeepU hs
  obtain ⟨tr, hsp', -, hrd, -, hvw, hnew⟩ := spinU_read (k := .acq) rfl
    (by rw [hrel]; exact relS_H hL) hsp hs
  have hKm := hsp.msg
  have hup' : UpTo σ'.snap.mem P.H K (· ≤ 3) := hup.snap hk.snap hKm
  have himp : ∀ u, lo u ≠ 0 → ¬ Pred.Pure (psiH P) u := fun u hu hp => hu (psiH_pure P hp)
  refine ⟨tr, hsp', hrd, hup'.extend fun t hKt htr u hr => ?_, fun hz => ?_⟩
  · by_cases hu : lo u = 0
    · rw [hu]; decide
    · obtain ⟨R, hR, -⟩ := hnew t u hKt htr hr (himp u hu)
      exact psiH_val hR
  · have hz' : UpTo σ'.snap.mem P.H K (· = 0) := UpTo.snap (hz : UpTo _ _ _ _) hk.snap hKm
    by_cases h1 : ∃ t u, K < t ∧ t ≤ tr ∧ σ'.snap.mem.read? P.H t = some u ∧ lo u = 1
    · obtain ⟨t, u, hKt, htr, hr, hu1⟩ := h1
      obtain ⟨R, hR, hcol⟩ := hnew t u hKt htr hr (himp u (by rw [hu1]; decide))
      rcases hR with ⟨h0, -⟩ | ⟨-, hB, hBX, hG⟩ | ⟨h23, -⟩
      · rw [hu1] at h0; exact absurd h0 (by decide)
      · obtain ⟨hq0, hq1, hX⟩ := hcol P.B0 hB
        exact .inr ⟨hq0, ⟨hq1, fun p hp => Nat.le_trans (hBX p ((hX p).mp hp)) (Nat.le_trans htr hvw)⟩,
          (hcol GB hG).2.1⟩
      · rw [hu1] at h23; rcases h23 with h | h <;> exact absurd h (by decide)
    · refine .inl (UpTo.extend hz' fun t hKt htr u hr => ?_)
      refine Classical.byContradiction fun hu => ?_
      obtain ⟨R, hR, -⟩ := hnew t u hKt htr hr (himp u hu)
      rcases hR with ⟨h0, -⟩ | ⟨hu1, -⟩ | ⟨-, t1, ht1, u1, hr1, hu1⟩
      · exact hu h0
      · exact h1 ⟨t, u, hKt, htr, hr, hu1⟩
      · rcases Nat.lt_or_ge K t1 with hK1 | hK1
        · exact h1 ⟨t1, u1, hK1, Nat.le_trans (Nat.le_of_lt ht1) htr, hr1, hu1⟩
        · have := hz' t1 hK1 u1 hr1; rw [hu1] at this; exact absurd this (by decide)

/-- **VC `LDAR X5, [X1]`** (the `head` spin of round `k`, with
`X4 = k - 1`): the back edge (`X4 - head = 2`) keeps `PR k`; the exit gives
`PX k`. Round 1 holds `B0` and so sees only `head = 0` (every message, read
or skipped); round 2 cannot loop (`head ≤ 3`); round 3 exits on
`head ≠ 0`, when `B0Back` must be `GotB0`. -/
theorem vcP_spin {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ σ' : State isa}
    {v : Val} (h : PR P k σ) (hs : (EP P tid).step (.load .acq false P.h 8) σ v σ') :
    (BitVec.ofNat 64 (k - 1) - lo v = 2#64 → PR P k σ') ∧ (BitVec.ofNat 64 (k - 1) - lo v ≠ 2#64 → PX P k σ') := by
  obtain ⟨hrel, hT, h1, h2, h3⟩ := h
  have hk := loadKeepU hs
  have hkr := hk.full
  have hT' : Hold P.T (σ'.vs.getCoh P.T) σ'.r := hT.keep hkr (hk.vs.coh _)
  have hvw := hk.vs.vwNew
  have hrel' : σ'.g.rel = relS P := by rw [hk.rel]; exact hrel
  have hback : ∀ {K tr}, (HZero P K σ → HZero P tr σ' ∨ ((σ.r.wr P.B0).q = 0 ∧ GotB0 P σ')) →
      B0Back P K σ → B0Back P tr σ' := fun hZ hz =>
    hz.elim (fun hg => .inl (hg.load hk)) fun hz => (hZ hz).elim .inr fun h => .inl h.2
  rcases hk3 with rfl | rfl | rfl
  · obtain ⟨hB0, hB1, hGA, K, hsp, hup, hz⟩ := h1 rfl
    obtain ⟨tr, hsp', hrd, hup', hZ⟩ := scanH hL hrel hsp hup hs
    rcases hZ hz with hz' | ⟨hq0, -⟩
    · have hv : lo v = 0 := hz' tr (Nat.le_refl _) v hrd
      refine ⟨fun he => absurd he (by rw [hv]; decide), fun _ => ⟨hrel', hT', ?_, fun _ => ?_,
        fun e => absurd e (by decide), fun e => absurd e (by decide)⟩⟩
      · rw [show slot P 1 = P.B0 from rfl]; exact hB0.keep hkr hvw
      · exact ⟨hB1.keep hkr hvw, q_keep hGA hkr, tr, hsp', hup', hz'⟩
    · rw [hB0.1] at hq0; exact absurd hq0 (by decide)
  · obtain ⟨hB1, hM, K, hsp, hup, hz⟩ := h2 rfl
    obtain ⟨tr, hsp', hrd, hup', hZ⟩ := scanH hL hrel hsp hup hs
    have hv3 : lo v ≤ 3 := hup' tr (Nat.le_refl _) v hrd
    refine ⟨fun he => absurd hv3 (by bv_omega), fun _ => ⟨hrel', hT', ?_, fun e => absurd e (by decide),
      fun _ => ⟨hM.load hk, tr, hsp', hup', hback hZ hz⟩, fun e => absurd e (by decide)⟩⟩
    rw [show slot P 2 = P.B1 from rfl]; exact hB1.keep hkr hvw
  · obtain ⟨hM, K, hsp, hup, hz⟩ := h3 rfl
    obtain ⟨tr, hsp', hrd, hup', hZ⟩ := scanH hL hrel hsp hup hs
    have hb := hback hZ hz
    refine ⟨fun _ => ⟨hrel', hT', fun e => absurd e (by decide), fun e => absurd e (by decide),
      fun _ => ⟨hM.load hk, tr, hsp', hup', hb⟩⟩, fun hne => ?_⟩
    rcases hb with ⟨hB0, hGB⟩ | hz'
    · exact ⟨hrel', hT', by rw [show slot P 3 = P.B0 from rfl]; exact hB0, fun e => absurd e (by decide),
        fun e => absurd e (by decide), fun _ => ⟨hGB, hM.load hk⟩⟩
    · have hv : lo v = 0 := hz' tr (Nat.le_refl _) v hrd
      exact (hne (by rw [hv]; decide)).elim

/-! ## The data store -/

/-- The `head` facts survive a store of the producer to another location. -/
theorem spinH_store {P : SP} {tid : Nat} {σ σ' : State isa} {k : StoreKind} {a : BitVec 64}
    {n : Nat} {v : Val} {b : Bool} (hs : (EP P tid).step (.store k false a n v) σ b σ') (hne : P.H ≠ ⟨a, n⟩)
    (hg : P.H ∉ (prodPlan P).gives ⟨a, n⟩ v) {Z Z' : Time → State isa → Prop}
    (hZ : ∀ K, SpinU P.H (psiH P) K σ → Z K σ → Z' K σ') (h : SpinH P Z σ) : SpinH P Z' σ' := by
  obtain ⟨K, hsp, hu, hz⟩ := h
  exact ⟨K, hsp.store_other hs hne (prod_whole _ _) hg,
    hu.prefix (snapLe_store hs) (hsp.msg.elim fun _ hr => read?_le_last hr), hZ K hsp hz⟩

theorem HZero.store {P : SP} {tid : Nat} {σ σ' : State isa} {k : StoreKind} {a : BitVec 64} {n : Nat} {v : Val}
    {b : Bool} {K : Time} (hs : (EP P tid).step (.store k false a n v) σ b σ') (hsp : SpinU P.H (psiH P) K σ)
    (h : HZero P K σ) : HZero P K σ' :=
  UpTo.prefix h (snapLe_store hs) (hsp.msg.elim fun _ hr => read?_le_last hr)

/-- **VC `STR W3, [X7]`** (the data store of round `k`, value `k`, to the
round's slot): permitted (unplanned, `emp` there), and gives `PD k`. -/
theorem vcP_storeB {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ : State isa} (h : PX P k σ) :
    (EP P tid).ok (.store .plain false (slot P k).addr 4 (nv k)) σ ∧
      ∀ b (σ' : State isa), (EP P tid).step (.store .plain false (slot P k).addr 4 (nv k)) σ b σ' → PD P k σ' := by
  obtain ⟨hrel, hT, hS, h1, h2, h3⟩ := h
  have hsT := slot_ne_T hL k
  have hsl : (⟨(slot P k).addr, 4⟩ : Loc) = slot P k := by unfold slot; split <;> rfl
  have hrl : (prodPlan P).rel (slot P k) (nv k) = false := prod_rel_ne hsT _
  have hgv : (prodPlan P).gives (slot P k) (nv k) = [] := prod_gives_ne hsT _
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · show 0 < (σ.r.wr ⟨(slot P k).addr, 4⟩).q
    rw [hsl, hS.1]; decide
  · intro _
    show Pred.Pure (σ.g.rel ⟨(slot P k).addr, 4⟩) _
    rw [hsl, hrel, relS_slot hL]; exact Pred.emp_pure _
  · intro hr
    change (prodPlan P).rel ⟨(slot P k).addr, 4⟩ (nv k) = true at hr
    rw [hsl, hrl] at hr; cases hr
  intro b σ' hs
  have hrel' := rel_store hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, ⟨Pc, -, hr⟩, -⟩ := step_storeFactsTU hs
  rw [hsl] at hr hwv hwb
  have hwh := prod_whole (P := P) (slot P k) (nv k)
  have hng : ∀ x, x ∉ (prodPlan P).gives (slot P k) (nv k) := by rw [hgv]; exact fun _ => List.not_mem_nil
  have hng' : ∀ x, x ∉ (prodPlan P).gives ⟨(slot P k).addr, 4⟩ (nv k) := by rw [hsl]; exact hng
  have hkf : ∀ x, x ≠ slot P k → (σ.r.wr x).q = 1 → (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (σ.r.wr x).X p :=
    fun x hx hq => by rw [hr]; exact keepsFull_store hx hwh (hng x) hq
  have hvw := hwv.mono.vwNew
  have hold : ∀ x, x ≠ slot P k → Hold x σ.vs.vwNew σ.r → Hold x σ'.vs.vwNew σ'.r := fun x hx hh =>
    ⟨(hkf x hx hh.1).1, fun p hp => Nat.le_trans (hh.2 p (((hkf x hx hh.1).2 p).mp hp)) hvw⟩
  have hq : ∀ x, x ≠ slot P k → (σ.r.wr x).q = 1 → (σ'.r.wr x).q = 1 := fun x hx hh => (hkf x hx hh).1
  have hHs : P.H ≠ ⟨(slot P k).addr, 4⟩ := by rw [hsl]; exact Ne.symm (slot_ne_H hL k)
  refine ⟨by rw [hrel']; exact hrel, ?_, ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨hq', hm⟩ := hT
    have := hkf P.T (Ne.symm hsT) hq'
    exact ⟨this.1, fun p hp => Nat.le_trans (hm p ((this.2 p).mp hp)) (hwv.mono.coh _)⟩
  · rw [hr]
    exact full_after hwh (hng _) hS.1 (fun p hp => Nat.lt_of_le_of_lt (hS.2 p hp) hwb.vwNew)
      (hwv.vwOld (by decide))
  · subst e
    obtain ⟨b1, g, d⟩ := h1 rfl
    exact ⟨hold _ (by rw [show slot P 1 = P.B0 from rfl]; exact (b0_b1 P).symm) b1,
      hq _ (by rw [show slot P 1 = P.B0 from rfl]; exact (ne_ga (by decide)).symm) g,
      spinH_store hs hHs (hng' _) (fun K hsp hz => hz.store hs hsp) d⟩
  · subst e
    obtain ⟨hM, d⟩ := h2 rfl
    refine ⟨hM.elim fun t ⟨u, hr, hu⟩ => ⟨t, u, msg_store hs hr, hu⟩,
      spinH_store hs hHs (hng' _) (fun K hsp hz => ?_) d⟩
    rcases hz with ⟨hB0, hGB⟩ | hz
    · exact .inl ⟨hold _ (by rw [show slot P 2 = P.B1 from rfl]; exact b0_b1 P) hB0,
        hq _ (by rw [show slot P 2 = P.B1 from rfl]; exact (ne_gb (by decide)).symm) hGB⟩
    · exact .inr (hz.store hs hsp)
  · subst e
    obtain ⟨g, hM⟩ := h3 rfl
    exact ⟨hq _ (by rw [show slot P 3 = P.B0 from rfl]; exact (ne_gb (by decide)).symm) g,
      hM.elim fun t ⟨u, hr, hu⟩ => ⟨t, u, msg_store hs hr, hu⟩⟩

#print axioms vcP_storeT
#print axioms vcP_spin
#print axioms vcP_storeB

end Kraken.Promising.SLR.EnvG.SpscA
