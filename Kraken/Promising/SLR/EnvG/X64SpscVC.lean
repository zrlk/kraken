/-
**Part 5: the SPSC invariants and VCs** on
`EnvGTX Arch.tso` over the layout `spscS = [b, b + 256, h, t]` (all words
of width `4`).

**Producer** (round `k = 1, 2, 3`; `eT k` the `tail` value before the round,
`tNew k` the one it writes, `slot k` the slot written):
- `PR k` (at `produce` and `pfull`): all of `T` with maximal write `eT k`
  (at or below `coh T`); round 1: all of `B0`, `B1`, `GA` and spin facts at
  `H` with last value `0`; round 2: all of `B1` and spin facts at `H` with
  last value `0`; round 3: all of `B0` and `GB`.
- `PX k` (after the spin's exit): round 2 has taken `B0` and `GB` from the
  consumer's `H := 1` (`psiH`, `spin_read`).
- `PD k` (after the data store): all of `slot k` with maximal write `k` at or
  below `vwOld`.
- `vcP_loadT` (`movl (%rdi), %eax`): `read_own`, exact (`psiT` impure).
  `vcP_spin` (`movl (%rsi), %edx`), `vcP_storeB` (`movl %r8d, (%rbx,%rdx,1)`),
  `vcP_storeT` (`movl %ecx, (%rdi)`, the planned release).

**Consumer** (round `k = 0, 1, 2`; `eC k` its `head` (and `eax`) in the
round, `hNew k` the `tail` value that ends the round's spin and the `head`
value it then writes, `cslot k` the slot read, `cval k = k + 1`):
- `CS` (at `consumer`), `CE k` (at `cempty k`), `CX k` (after the spin's
  exit: all of `cslot k` with maximal write `cval k` at or below `vrNew` and
  `vwNew`).
- `vcC_loadH` (`movl (%rsi), %eax`: `read_own`, `0`), `vcC_spin`,
  `vcC_data` (under the clean flag the data load returns `cval k`,
  `read_max`), `vcC_storeH`.

Every predicate is monotone under fences (`….fence`).
-/
import Kraken.Promising.SLR.EnvG.X64SpscRead
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

/-! ## The layout and the environments -/

/-- The shared layout: the two slots and the two indices. -/
abbrev spscS (P : SP) : SharedEnv.Layout := [(P.b, 4), (P.b + 256, 4), (P.h, 4), (P.t, 4)]

theorem spscS_le16 (P : SP) : Le16 (spscS P) := fun x hx => by
  simp only [spscS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact (by decide : 4 ≤ 16)

/-- The producer's environment. -/
abbrev EP (P : SP) (tid : Nat) : SharedEnv := EnvGTX Arch.tso tid (prodPlan P) (spscS P)

/-- The consumer's environment. -/
abbrev EC (P : SP) (tid : Nat) : SharedEnv := EnvGTX Arch.tso tid (consPlan P) (spscS P)

/-! ## Ownership facts -/

-- `Hold` … `wr_after_ne`: the ISA-neutral `SpscCommon` facts.
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.Full ↦ Kraken.Promising.X64.EnvG.SpscX.Full,
  Kraken.Promising.SLR.EnvG.SpscCommon.KeepsFull ↦ Kraken.Promising.X64.EnvG.SpscX.KeepsFull,
  Kraken.Promising.SLR.EnvG.SpscCommon.Hold ↦ Kraken.Promising.X64.EnvG.SpscX.Hold,
  Kraken.Promising.SLR.EnvG.SpscCommon.Hold.mono ↦ Kraken.Promising.X64.EnvG.SpscX.Hold.mono,
  Kraken.Promising.SLR.EnvG.SpscCommon.Hold.keep ↦ Kraken.Promising.X64.EnvG.SpscX.Hold.keep,
  Kraken.Promising.SLR.EnvG.SpscCommon.Full.mono ↦ Kraken.Promising.X64.EnvG.SpscX.Full.mono,
  Kraken.Promising.SLR.EnvG.SpscCommon.Full.keep ↦ Kraken.Promising.X64.EnvG.SpscX.Full.keep,
  Kraken.Promising.SLR.EnvG.SpscCommon.q_keep ↦ Kraken.Promising.X64.EnvG.SpscX.q_keep,
  Kraken.Promising.SLR.EnvG.SpscCommon.wr_after_ne ↦ Kraken.Promising.X64.EnvG.SpscX.wr_after_ne,
  Kraken.Promising.SLR.EnvG.SpscCommon.wr_only_mem ↦ Kraken.Promising.X64.EnvG.SpscX.wr_only_mem,
  Kraken.Promising.SLR.EnvG.SpscCommon.min_mono ↦ Kraken.Promising.X64.EnvG.SpscX.min_mono]

/-! ## The plans at the SPSC stores -/

section Plans

variable {P : SP}

theorem prod_whole (l : Loc) (v : Val) : (prodPlan P).Whole l v :=
  Plan.Whole.of_entries (fun e he => by
    simp only [prodPlan, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl) l v

theorem cons_whole (l : Loc) (v : Val) : (consPlan P).Whole l v :=
  Plan.Whole.of_entries (fun e he => by
    simp only [consPlan, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; rfl) l v

theorem prod_rel_ne {x : Loc} (hx : x ≠ P.T) (v : Val) : (prodPlan P).rel x v = false := by
  simp [prodPlan, Plan.rel, Plan.find?, Ne.symm hx]

theorem prod_gives_ne {x : Loc} (hx : x ≠ P.T) (v : Val) : (prodPlan P).gives x v = [] := by
  simp [prodPlan, Plan.gives, Plan.find?, Ne.symm hx]

theorem prod_rel_T1 : (prodPlan P).rel P.T 1#128 = true := by simp [prodPlan, Plan.rel, Plan.find?]
theorem prod_gives_T1 : (prodPlan P).gives P.T 1#128 = [P.B0, GA, GB] := by simp [prodPlan, Plan.gives, Plan.find?]
theorem prod_rel_T0 : (prodPlan P).rel P.T 0#128 = true := by simp [prodPlan, Plan.rel, Plan.find?]
theorem prod_gives_T0 : (prodPlan P).gives P.T 0#128 = [P.B1] := by simp [prodPlan, Plan.gives, Plan.find?]

theorem cons_rel_ne {x : Loc} (hx : x ≠ P.H) (v : Val) : (consPlan P).rel x v = false := by
  simp [consPlan, Plan.rel, Plan.find?, Ne.symm hx]

theorem cons_rel_H1 : (consPlan P).rel P.H 1#128 = true := by simp [consPlan, Plan.rel, Plan.find?]
theorem cons_gives_H1 : (consPlan P).gives P.H 1#128 = [P.B0, GB] := by simp [consPlan, Plan.gives, Plan.find?]
theorem cons_rel_H0 : (consPlan P).rel P.H 0#128 = false := by simp [consPlan, Plan.rel, Plan.find?]
theorem cons_gives_H0 : (consPlan P).gives P.H 0#128 = [] := by simp [consPlan, Plan.gives, Plan.find?]

end Plans

theorem after_rel {pl : Plan} {l : Loc} {v : Val} {tw : Time} {cl : Prop} {r : Res} (h : pl.rel l v = true)
    (hw : pl.Whole l v) : pl.after l v tw cl r = (Res.drop (pl.gives l v) r).addW l (v, tw) := by
  unfold Plan.after; simp only [h, ↓reduceIte, pl.keep_of_whole hw]

theorem after_norel {pl : Plan} {l : Loc} {v : Val} {tw : Time} {cl : Prop} {r : Res} (h : pl.rel l v = false) :
    pl.after l v tw cl r = r.addW l (v, tw) := by
  unfold Plan.after; simp only [h, Bool.false_eq_true, ↓reduceIte]

hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.Full ↦ Kraken.Promising.X64.EnvG.SpscX.Full,
  Kraken.Promising.SLR.EnvG.SpscCommon.keepsFull_store ↦ Kraken.Promising.X64.EnvG.SpscX.keepsFull_store,
  Kraken.Promising.SLR.EnvG.SpscCommon.full_after ↦ Kraken.Promising.X64.EnvG.SpscX.full_after]

/-- The release predicates over a store's anchor. -/
theorem rel_store {A : Arch} {pl : Plan} {S : SharedEnv.Layout} {tid : Nat} {σ σ' : EStateX} {k : StoreKind}
    {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (hs : (EnvGTX A tid pl S).step (.store k xcl a n v) σ b σ') : σ'.g.rel = σ.g.rel := by
  obtain ⟨c, tw, hanc, -⟩ := step_storeFactsT hs
  exact hanc.rel

/-! ## The producer's values -/

/-- `tail` before producer round `k` (`0, 1, 0`). -/
def eT (k : Nat) : Val := if k = 2 then 1#128 else 0#128

/-- `tail` written in producer round `k` (`1, 0, 1`). -/
def tNew (k : Nat) : Val := if k = 2 then 0#128 else 1#128

/-- The slot written in producer round `k`. -/
def slot (P : SP) (k : Nat) : Loc := if k = 2 then P.B1 else P.B0

/-- The value written in producer round `k`. -/
def kval (k : Nat) : Val := BitVec.ofNat 128 k

/-! ## The producer's invariants -/

/-- **At `produce` and `pfull`** of round `k`. -/
def PR (P : SP) (k : Nat) (σ : EStateX) : Prop :=
  σ.g.rel = relS P ∧ Full P.T (eT k) (σ.vs.getCoh P.T) σ.r ∧
    (k = 1 → Hold P.B0 σ.vs.vwNew σ.r ∧ Hold P.B1 σ.vs.vwNew σ.r ∧ (σ.r.wr GA).q = 1 ∧
      ∃ K, SpinAt P.H (psiH P) K 0#128 σ) ∧
    (k = 2 → Hold P.B1 σ.vs.vwNew σ.r ∧ ∃ K, SpinAt P.H (psiH P) K 0#128 σ) ∧
    (k = 3 → Hold P.B0 σ.vs.vwNew σ.r ∧ (σ.r.wr GB).q = 1)

/-- **After the spin's exit** in round `k`. -/
def PX (P : SP) (k : Nat) (σ : EStateX) : Prop :=
  σ.g.rel = relS P ∧ Full P.T (eT k) (σ.vs.getCoh P.T) σ.r ∧ Hold (slot P k) σ.vs.vwNew σ.r ∧
    (k = 1 → Hold P.B1 σ.vs.vwNew σ.r ∧ (σ.r.wr GA).q = 1 ∧ ∃ K, SpinAt P.H (psiH P) K 0#128 σ) ∧
    (k = 2 → Hold P.B0 σ.vs.vwNew σ.r ∧ (σ.r.wr GB).q = 1) ∧
    (k = 3 → (σ.r.wr GB).q = 1)

/-- **After the data store** in round `k`. -/
def PD (P : SP) (k : Nat) (σ : EStateX) : Prop :=
  σ.g.rel = relS P ∧ Full P.T (eT k) (σ.vs.getCoh P.T) σ.r ∧ Full (slot P k) (kval k) σ.vs.vwOld σ.r ∧
    (k = 1 → Hold P.B1 σ.vs.vwNew σ.r ∧ (σ.r.wr GA).q = 1 ∧ ∃ K, SpinAt P.H (psiH P) K 0#128 σ) ∧
    (k = 2 → Hold P.B0 σ.vs.vwNew σ.r ∧ (σ.r.wr GB).q = 1) ∧
    (k = 3 → (σ.r.wr GB).q = 1)

/-! ### Fences -/

section Fence

variable {P : SP} {k : Nat} {σ σ' : EStateX}

hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.KeepsFull ↦ Kraken.Promising.X64.EnvG.SpscX.KeepsFull,
  Kraken.Promising.SLR.EnvG.SpscCommon.keepsFull_refl ↦ Kraken.Promising.X64.EnvG.SpscX.keepsFull_refl]

theorem PR.fence (h : PR P k σ) (hf : FenceLe σ σ') : PR P k σ' := by
  obtain ⟨hrel, hT, h1, h2, h3⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  refine ⟨by rw [hf.g]; exact hrel, hT.keep hk (Nat.le_of_eq (hf.getCoh _).symm), fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨a, b, c, K, d⟩ := h1 e
    exact ⟨a.keep hk hf.vwNew, b.keep hk hf.vwNew, q_keep c hk, K, d.fence hf⟩
  · obtain ⟨a, K, d⟩ := h2 e
    exact ⟨a.keep hk hf.vwNew, K, d.fence hf⟩
  · obtain ⟨a, b⟩ := h3 e
    exact ⟨a.keep hk hf.vwNew, q_keep b hk⟩

theorem PX.fence (h : PX P k σ) (hf : FenceLe σ σ') : PX P k σ' := by
  obtain ⟨hrel, hT, hs, h1, h2, h3⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  refine ⟨by rw [hf.g]; exact hrel, hT.keep hk (Nat.le_of_eq (hf.getCoh _).symm), hs.keep hk hf.vwNew, fun e => ?_,
    fun e => ?_, fun e => q_keep (h3 e) hk⟩
  · obtain ⟨b, c, K, d⟩ := h1 e
    exact ⟨b.keep hk hf.vwNew, q_keep c hk, K, d.fence hf⟩
  · obtain ⟨a, b⟩ := h2 e
    exact ⟨a.keep hk hf.vwNew, q_keep b hk⟩

theorem PD.fence (h : PD P k σ) (hf : FenceLe σ σ') : PD P k σ' := by
  obtain ⟨hrel, hT, hs, h1, h2, h3⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  refine ⟨by rw [hf.g]; exact hrel, hT.keep hk (Nat.le_of_eq (hf.getCoh _).symm), hs.keep hk (Nat.le_of_eq hf.vwOld.symm), fun e => ?_,
    fun e => ?_, fun e => q_keep (h3 e) hk⟩
  · obtain ⟨b, c, K, d⟩ := h1 e
    exact ⟨b.keep hk hf.vwNew, q_keep c hk, K, d.fence hf⟩
  · obtain ⟨a, b⟩ := h2 e
    exact ⟨a.keep hk hf.vwNew, q_keep b hk⟩

end Fence

/-! ### Loads keep the producer's facts -/

theorem PR.load {P : SP} {k tid : Nat} {l : Loc} {σ σ' : EStateX} (h : PR P k σ) (hk : LoadKeep tid l σ σ')
    (hl : P.H ≠ l) : PR P k σ' := by
  obtain ⟨hrel, hT, h1, h2, h3⟩ := h
  refine ⟨by rw [hk.rel]; exact hrel, hT.keep hk.full (hk.vs.coh _), fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨a, b, c, K, d⟩ := h1 e
    exact ⟨a.keep hk.full hk.vs.vwNew, b.keep hk.full hk.vs.vwNew, q_keep c hk.full, K, d.load_other hk hl⟩
  · obtain ⟨a, K, d⟩ := h2 e
    exact ⟨a.keep hk.full hk.vs.vwNew, K, d.load_other hk hl⟩
  · obtain ⟨a, b⟩ := h3 e
    exact ⟨a.keep hk.full hk.vs.vwNew, q_keep b hk.full⟩

/-! ### The VCs -/

/-- **VC `movl (%rdi), %eax`**: the producer reads its own `tail` exactly
(`read_own`, `psiT` impure) and keeps `PR`. -/
theorem vcP_loadT {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ σ' : EStateX} {v : Val} (h : PR P k σ)
    (hs : (EP P tid).step (.load .plain false P.t 4) σ v σ') : v = eT k ∧ PR P k σ' := by
  refine ⟨?_, h.load (loadKeep hs) hL.h_t⟩
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, -⟩ := step_loadFactsT (pl := prodPlan P) hs
  obtain ⟨hrel, ⟨hq, ts, hX, hmax, hts⟩, -⟩ := h
  rcases read_own E hanc.lt hq hX hmax hrd.val hrd.window (Nat.le_trans hts (Nat.le_max_right _ _)) with
    ⟨-, rfl⟩ | ⟨-, hp⟩
  · rfl
  · rw [hanc.rel, hrel, relS_T] at hp; exact absurd hp (psiT_impure P v)

/-- `psiH`'s values. -/
theorem psiH_val {P : SP} {v : Val} {m : Memory} {V : View} {R : Res} (h : (psiH P).P v m V R) :
    v = 1#128 ∨ v = 0#128 :=
  h.imp (·.1) (·.1)

/-- **VC `movl (%rsi), %edx`** (the `pfull` spin of round `k`): on the
back edge (`edx = ecx = tNew k`) `PR` again; at the exit `PX`. -/
theorem vcP_spin {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ σ' : EStateX}
    {v : Val} (h : PR P k σ) (hs : (EP P tid).step (.load .plain false P.h 4) σ v σ') :
    (v.setWidth 32 = (tNew k).setWidth 32 → PR P k σ') ∧ (v.setWidth 32 ≠ (tNew k).setWidth 32 → PX P k σ') := by
  have hk := loadKeep hs
  have hHT := hL.h_t
  obtain ⟨hrel, hT, h1, h2, h3⟩ := h
  have hrelH : σ.g.rel P.H = psiH P := by rw [hrel, relS_H hL]
  have hrel' : σ'.g.rel = relS P := by rw [hk.rel]; exact hrel
  have hT' := hT.keep hk.full (hk.vs.coh _)
  rcases hk3 with rfl | rfl | rfl
  · obtain ⟨hB0, hB1, hGA, K, hsp⟩ := h1 rfl
    obtain ⟨tr, hsp', -, hv⟩ := spin_read hrelH hsp hs
    have hv0 : v = 0#128 := by
      rcases hv with ⟨-, rfl⟩ | ⟨-, hp⟩ | ⟨-, R, hR, hex, -⟩
      · rfl
      · exact psiH_pure P hp
      · rcases hR with ⟨rfl, hq, -⟩ | ⟨rfl, -⟩
        · have := (hex _ hq).1; rw [hB0.1] at this; exact absurd this (by decide)
        · rfl
    subst hv0
    refine ⟨fun e => absurd e (by decide), fun _ => ⟨hrel', hT', hB0.keep hk.full hk.vs.vwNew,
      fun _ => ⟨hB1.keep hk.full hk.vs.vwNew, q_keep hGA hk.full, tr, hsp'⟩, fun e => absurd e (by decide),
      fun e => absurd e (by decide)⟩⟩
  · obtain ⟨hB1, K, hsp⟩ := h2 rfl
    obtain ⟨tr, hsp', -, hv⟩ := spin_read hrelH hsp hs
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have hv0 : v = 0#128 := by
        rcases hv with ⟨-, rfl⟩ | ⟨-, hp⟩ | ⟨-, R, hR, -⟩
        · rfl
        · exact psiH_pure P hp
        · rcases hR with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact absurd e (by decide)
          · rfl
      subst hv0
      exact ⟨hrel', hT', fun e => absurd e (by decide), fun _ => ⟨hB1.keep hk.full hk.vs.vwNew, tr, hsp'⟩,
        fun e => absurd e (by decide)⟩
    · rcases hv with ⟨-, rfl⟩ | ⟨-, hp⟩ | ⟨hlt, R, hR, hex, -, hvw⟩
      · exact absurd rfl e
      · rw [psiH_pure P hp] at e; exact absurd rfl e
      · rcases hR with ⟨rfl, hq0, hX0, hqB⟩ | ⟨rfl, -⟩
        · obtain ⟨-, hq0', hX0'⟩ := hex _ hq0
          refine ⟨hrel', hT', hB1.keep hk.full hk.vs.vwNew, fun e => absurd e (by decide),
            fun _ => ⟨⟨hq0', fun p hp => Nat.le_trans (hX0 p ((hX0' p).mp hp)) hvw⟩, (hex _ hqB).2.1⟩,
            fun e => absurd e (by decide)⟩
        · exact absurd rfl e
  · obtain ⟨hB0, hGB⟩ := h3 rfl
    have hB0' := hB0.keep hk.full hk.vs.vwNew
    have hGB' := q_keep hGB hk.full
    exact ⟨fun _ => ⟨hrel', hT', fun e => absurd e (by decide), fun e => absurd e (by decide), fun _ => ⟨hB0', hGB'⟩⟩,
      fun _ => ⟨hrel', hT', hB0', fun e => absurd e (by decide), fun e => absurd e (by decide), fun _ => hGB'⟩⟩

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

/-- **VC `movl %r8d, (%rbx,%rdx,1)`** (the data store of round `k`):
permitted (unplanned, pure), and gives `PD`. -/
theorem vcP_storeB {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ : EStateX} (h : PX P k σ) :
    (EP P tid).ok (.store .plain false (slot P k).addr 4 (kval k)) σ ∧
      ∀ b (σ' : EStateX), (EP P tid).step (.store .plain false (slot P k).addr 4 (kval k)) σ b σ' → PD P k σ' := by
  obtain ⟨hrel, hT, hS, h1, h2, h3⟩ := h
  have hsT := slot_ne_T hL k
  have hsl : (⟨(slot P k).addr, 4⟩ : Loc) = slot P k := by unfold slot; split <;> rfl
  have hrl : (prodPlan P).rel (slot P k) (kval k) = false := prod_rel_ne hsT _
  have hgv : (prodPlan P).gives (slot P k) (kval k) = [] := prod_gives_ne hsT _
  refine ⟨⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · show 0 < (σ.r.wr ⟨(slot P k).addr, 4⟩).q
    rw [hsl, hS.1]; decide
  · intro _
    show Pred.Pure (σ.g.rel ⟨(slot P k).addr, 4⟩) _
    rw [hsl, hrel, relS_slot hL]; exact Pred.emp_pure _
  · intro hr
    change (prodPlan P).rel ⟨(slot P k).addr, 4⟩ (kval k) = true at hr
    rw [hsl, hrl] at hr; cases hr
  · unfold slot; split <;> simp [SharedEnv.AccessIn]
  intro b σ' hs
  have hrel' := rel_store hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, ⟨Pc, -, hr⟩, -⟩ := step_storeFactsT hs
  rw [hsl] at hr hwv hwb
  have hwh := prod_whole (P := P) (slot P k) (kval k)
  have hng : ∀ x, x ∉ (prodPlan P).gives (slot P k) (kval k) := by rw [hgv]; exact fun _ => List.not_mem_nil
  have hkf : ∀ x, x ≠ slot P k → (σ.r.wr x).q = 1 → (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (σ.r.wr x).X p :=
    fun x hx hq => by rw [hr]; exact keepsFull_store hx hwh (hng x) hq
  have hvw := hwv.mono.vwNew
  have hold : ∀ x, x ≠ slot P k → Hold x σ.vs.vwNew σ.r → Hold x σ'.vs.vwNew σ'.r := fun x hx hh =>
    ⟨(hkf x hx hh.1).1, fun p hp => Nat.le_trans (hh.2 p (((hkf x hx hh.1).2 p).mp hp)) hvw⟩
  have hq : ∀ x, x ≠ slot P k → (σ.r.wr x).q = 1 → (σ'.r.wr x).q = 1 := fun x hx hh => (hkf x hx hh).1
  refine ⟨by rw [hrel']; exact hrel, ?_, ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨hq', ts, hX, hm, hts⟩ := hT
    have := hkf P.T (Ne.symm hsT) hq'
    exact ⟨this.1, ts, (this.2 _).mpr hX, fun p hp => hm p ((this.2 p).mp hp), Nat.le_trans hts (hwv.mono.coh _)⟩
  · rw [hr]
    exact full_after hwh (hng _) hS.1 (fun p hp => Nat.lt_of_le_of_lt (hS.2 p hp) hwb.vwNew) (hwv.vwOld (by decide))
  · subst e
    obtain ⟨b1, g, K, d⟩ := h1 rfl
    exact ⟨hold _ (by unfold slot; simp) b1, hq _ (by unfold slot; simp) g,
      K, d.store_other hs (by rw [hsl]; exact Ne.symm (slot_ne_H hL 1)) (by rw [hsl]; exact hwh)
        (by rw [hsl]; exact hng _)⟩
  · subst e
    obtain ⟨b0, g⟩ := h2 rfl
    exact ⟨hold _ (by unfold slot; simp) b0, hq _ (by unfold slot; simp) g⟩
  · subst e
    exact hq _ (by unfold slot; simp) (h3 rfl)

/-- **VC `movl %ecx, (%rdi)`** (the `tail` release of round `k`): permitted
(planned, `psiT` impure, `T` kept, the slot written (and the token) satisfy
`psiT`), and gives `PR (k + 1)` (rounds 1, 2) and all of `T`. -/
theorem vcP_storeT {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ : EStateX}
    (h : PD P k σ) :
    (EP P tid).ok (.store .plain false P.t 4 (tNew k)) σ ∧
      ∀ b (σ' : EStateX), (EP P tid).step (.store .plain false P.t 4 (tNew k)) σ b σ' →
        (k = 1 → PR P 2 σ') ∧ (k = 2 → PR P 3 σ') ∧ (σ'.r.wr P.T).q = 1 := by
  obtain ⟨hrel, ⟨hqT, tsT, hXT, hmT, htsT⟩, hS, h1, h2, h3⟩ := h
  have hrl : (prodPlan P).rel P.T (tNew k) = true := by
    rcases hk3 with rfl | rfl | rfl
    · exact prod_rel_T1
    · exact prod_rel_T0
    · exact prod_rel_T1
  have hwh := prod_whole (P := P) P.T (tNew k)
  have hTg : P.T ∉ (prodPlan P).gives P.T (tNew k) := (prodPlan_valid hL).not_mem_gives _ _
  refine ⟨⟨⟨rfl, by show 0 < (σ.r.wr P.T).q; rw [hqT]; decide, fun hr => absurd (hr.symm.trans hrl) Bool.false_ne_true,
    fun _ => ⟨.inl rfl, by show ¬ Pred.Pure (σ.g.rel P.T) _; rw [hrel, relS_T]; exact psiT_impure P _, hTg, ?_⟩⟩,
    by simp [SharedEnv.AccessIn]⟩, ?_⟩
  · intro c g _ hwb
    have hlt := hwb.rel rfl
    show (σ.g.rel P.T).P _ _ _ _
    rw [hrel, relS_T, Plan.give_of_whole _ hwh]
    obtain ⟨hqS, ts, hX, hm, hts⟩ := hS
    have hV : ts ≤ c.mem.last + 1 := by simp only [Time, View] at *; omega
    rcases hk3 with rfl | rfl | rfl
    · obtain ⟨-, hGA, -⟩ := h1 rfl
      rw [show tNew 1 = 1#128 from rfl, prod_gives_T1]
      have e1 : P.B0 ∈ [P.B0, GA, GB] := by simp
      have e2 : GA ∈ [P.B0, GA, GB] := by simp
      refine .inl ⟨rfl, .inl ⟨⟨by rw [wr_only_mem e1]; exact hqS, ts, by rw [wr_only_mem e1]; exact hX,
        fun p hp => hm p (by rw [wr_only_mem e1] at hp; exact hp), hV⟩, by rw [wr_only_mem e2]; exact hGA⟩⟩
    · rw [show tNew 2 = 0#128 from rfl, prod_gives_T0]
      have e1 : P.B1 ∈ [P.B1] := by simp
      refine .inr ⟨rfl, .inr ⟨by rw [wr_only_mem e1]; exact hqS, ts, by rw [wr_only_mem e1]; exact hX,
        fun p hp => hm p (by rw [wr_only_mem e1] at hp; exact hp), hV⟩⟩
    · have hGB := h3 rfl
      rw [show tNew 3 = 1#128 from rfl, prod_gives_T1]
      have e1 : P.B0 ∈ [P.B0, GA, GB] := by simp
      have e3 : GB ∈ [P.B0, GA, GB] := by simp
      refine .inl ⟨rfl, .inr ⟨⟨by rw [wr_only_mem e1]; exact hqS, ts, by rw [wr_only_mem e1]; exact hX,
        fun p hp => hm p (by rw [wr_only_mem e1] at hp; exact hp), hV⟩, by rw [wr_only_mem e3]; exact hGB⟩⟩
  intro b σ' hs
  have hrel' := rel_store hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, ⟨Pc, -, hr⟩, -⟩ := step_storeFactsT hs
  have hTfull : Full P.T (tNew k) (σ'.vs.getCoh P.T) σ'.r := by
    rw [hr]
    exact full_after hwh hTg hqT (fun p hp => Nat.lt_of_le_of_lt (Nat.le_trans (hmT p hp) htsT) hwb.coh) hwv.coh
  have hkf : ∀ x, x ≠ P.T → x ∉ (prodPlan P).gives P.T (tNew k) → (σ.r.wr x).q = 1 →
      (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (σ.r.wr x).X p :=
    fun x hx hg hq => by rw [hr]; exact keepsFull_store hx hwh hg hq
  have hvw := hwv.mono.vwNew
  refine ⟨fun e => ?_, fun e => ?_, hTfull.1⟩
  · subst e
    obtain ⟨hB1, hGA, K, hsp⟩ := h1 rfl
    have hg : P.B1 ∉ (prodPlan P).gives P.T (tNew 1) := by
      show P.B1 ∉ (prodPlan P).gives P.T 1#128
      rw [prod_gives_T1]; simp [Ne.symm (b0_b1 P)]
    have hgH : P.H ∉ (prodPlan P).gives P.T (tNew 1) := by
      show P.H ∉ (prodPlan P).gives P.T 1#128
      rw [prod_gives_T1]; simp [hL.b0_h.symm]
    have hB1' := hkf P.B1 hL.b1_t hg hB1.1
    exact ⟨by rw [hrel']; exact hrel, hTfull, fun e => absurd e (by decide),
      fun _ => ⟨⟨hB1'.1, fun p hp => Nat.le_trans (hB1.2 p ((hB1'.2 p).mp hp)) hvw⟩, K,
        hsp.store_other hs hL.h_t hwh hgH⟩, fun e => absurd e (by decide)⟩
  · subst e
    obtain ⟨hB0, hGB⟩ := h2 rfl
    have hg0 : P.B0 ∉ (prodPlan P).gives P.T (tNew 2) := by
      show P.B0 ∉ (prodPlan P).gives P.T 0#128
      rw [prod_gives_T0]; simp [b0_b1 P]
    have hgB : GB ∉ (prodPlan P).gives P.T (tNew 2) := by
      show GB ∉ (prodPlan P).gives P.T 0#128
      rw [prod_gives_T0]; simp [ne_gb.symm]
    have hB0' := hkf P.B0 hL.b0_t hg0 hB0.1
    exact ⟨by rw [hrel']; exact hrel, hTfull, fun e => absurd e (by decide), fun e => absurd e (by decide),
      fun _ => ⟨⟨hB0'.1, fun p hp => Nat.le_trans (hB0.2 p ((hB0'.2 p).mp hp)) hvw⟩,
        (hkf GB ne_gb.symm hgB hGB).1⟩⟩

/-! ## The consumer's values -/

/-- `head` (and `eax`) in consumer round `k` (`0, 1, 0`). -/
def eC (k : Nat) : Val := if k = 1 then 1#128 else 0#128

/-- The `tail` value that ends the spin of consumer round `k`, and the `head`
value the round then writes (`1, 0, 1`). -/
def hNew (k : Nat) : Val := if k = 1 then 0#128 else 1#128

/-- The slot read in consumer round `k`. -/
def cslot (P : SP) (k : Nat) : Loc := if k = 1 then P.B1 else P.B0

/-- The value read in consumer round `k`. -/
def cval (k : Nat) : Val := BitVec.ofNat 128 (k + 1)

/-! ## The consumer's invariants -/

/-- **At `consumer`**: all of `H` (initial value `0`), `GB`, spin facts at `T`. -/
def CS (P : SP) (σ : EStateX) : Prop :=
  σ.g.rel = relS P ∧ Full P.H 0#128 (σ.vs.getCoh P.H) σ.r ∧ (σ.r.wr GB).q = 1 ∧
    ∃ K, SpinAt P.T (psiT P) K 0#128 σ

/-- **At `cempty k`.** -/
def CE (P : SP) (k : Nat) (σ : EStateX) : Prop :=
  σ.g.rel = relS P ∧ (σ.r.wr P.H).q = 1 ∧ (∃ K, SpinAt P.T (psiT P) K (eC k) σ) ∧
    (k = 0 → (σ.r.wr GB).q = 1) ∧ (k ≠ 0 → (σ.r.wr GA).q = 1)

/-- **After the spin's exit** in round `k`. -/
def CX (P : SP) (k : Nat) (σ : EStateX) : Prop :=
  σ.g.rel = relS P ∧ (σ.r.wr P.H).q = 1 ∧ (k ≠ 2 → ∃ K, SpinAt P.T (psiT P) K (hNew k) σ) ∧
    Full (cslot P k) (cval k) (min σ.vs.vrNew σ.vs.vwNew) σ.r ∧ (σ.r.wr GA).q = 1 ∧
    (k ≠ 1 → (σ.r.wr GB).q = 1)

/-! ### Fences -/

section CFence

variable {P : SP} {k : Nat} {σ σ' : EStateX}

theorem CS.fence (h : CS P σ) (hf : FenceLe σ σ') : CS P σ' := by
  obtain ⟨hrel, hH, hGB, K, hsp⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  exact ⟨by rw [hf.g]; exact hrel, hH.keep hk (Nat.le_of_eq (hf.getCoh _).symm), q_keep hGB hk, K, hsp.fence hf⟩

theorem CE.fence (h : CE P k σ) (hf : FenceLe σ σ') : CE P k σ' := by
  obtain ⟨hrel, hH, ⟨K, hsp⟩, h0, h1⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  exact ⟨by rw [hf.g]; exact hrel, q_keep hH hk, ⟨K, hsp.fence hf⟩, fun e => q_keep (h0 e) hk,
    fun e => q_keep (h1 e) hk⟩

theorem CX.fence (h : CX P k σ) (hf : FenceLe σ σ') : CX P k σ' := by
  obtain ⟨hrel, hH, hsp, hS, hGA, hGB⟩ := h
  have hk : KeepsFull σ.r σ'.r := by rw [hf.r]; exact keepsFull_refl _
  exact ⟨by rw [hf.g]; exact hrel, q_keep hH hk, fun e => (hsp e).elim fun K h => ⟨K, h.fence hf⟩,
    hS.keep hk (min_mono hf.vrNew hf.vwNew), q_keep hGA hk, fun e => q_keep (hGB e) hk⟩

end CFence

/-! ### The VCs -/

/-- **VC `movl (%rsi), %eax`** (the consumer's first load): it reads `head`
exactly `0` (`read_own`; later messages are pure, and `psiH` is pure only at
`0`). -/
theorem vcC_loadH {P : SP} (hL : SpscLocs P) {tid : Nat} {σ σ' : EStateX} {v : Val} (h : CS P σ)
    (hs : (EC P tid).step (.load .plain false P.h 4) σ v σ') : v = 0#128 ∧ CE P 0 σ' := by
  have hk := loadKeep hs
  obtain ⟨hrel, ⟨hq, ts, hX, hmax, hts⟩, hGB, K, hsp⟩ := h
  refine ⟨?_, by rw [hk.rel]; exact hrel, q_keep hq hk.full, ⟨K, hsp.load_other hk (Ne.symm hL.h_t)⟩,
    fun _ => q_keep hGB hk.full, fun e => absurd rfl e⟩
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, -⟩ := step_loadFactsT (pl := consPlan P) hs
  rcases read_own E hanc.lt hq hX hmax hrd.val hrd.window (Nat.le_trans hts (Nat.le_max_right _ _)) with
    ⟨-, rfl⟩ | ⟨-, hp⟩
  · rfl
  · rw [hanc.rel, hrel, relS_H hL] at hp; exact psiH_pure P hp

/-- `psiT`'s values. -/
theorem psiT_val {P : SP} {v : Val} {m : Memory} {V : View} {R : Res} (h : (psiT P).P v m V R) :
    v = 1#128 ∨ v = 0#128 :=
  h.imp (·.1) (·.1)

theorem low32_one_ne_zero : (1#128 : Val).setWidth 32 ≠ (0#128 : Val).setWidth 32 := by decide

/-- **VC `movl (%rdi), %ecx`** (the `cempty k` spin): on the back edge
(`ecx = eax = eC k`) `CE` again; at the exit `CX`, having taken the round's
slot (`psiT`; the other disjunct is excluded by the token the consumer
holds). -/
theorem vcC_spin {P : SP} {tid k : Nat} (hk3 : k = 0 ∨ k = 1 ∨ k = 2) {σ σ' : EStateX}
    {v : Val} (h : CE P k σ) (hs : (EC P tid).step (.load .plain false P.t 4) σ v σ') :
    (v.setWidth 32 = (eC k).setWidth 32 → CE P k σ') ∧ (v.setWidth 32 ≠ (eC k).setWidth 32 → CX P k σ') := by
  have hk := loadKeep hs
  obtain ⟨hrel, hH, ⟨K, hsp⟩, h0, h1⟩ := h
  have hrelT : σ.g.rel P.T = psiT P := by rw [hrel, relS_T]
  have hrel' : σ'.g.rel = relS P := by rw [hk.rel]; exact hrel
  have hH' := q_keep hH hk.full
  obtain ⟨tr, hsp', -, hv⟩ := spin_read hrelT hsp hs
  have hvals : v = eC k ∨ (K < tr ∧ ∃ R, (psiT P).P v σ'.snap.mem tr R ∧
      (∀ x, (R.wr x).q = 1 → (σ.r.wr x).q = 0 ∧ (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (R.wr x).X p) ∧
      tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew) := by
    rcases hv with ⟨-, rfl⟩ | ⟨-, hp⟩ | h
    · exact .inl rfl
    · exact absurd hp (psiT_impure P v)
    · exact .inr h
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have hv' : v = eC k := by
      rcases hvals with h | ⟨-, R, hR, -⟩
      · exact h
      · rcases hk3 with rfl | rfl | rfl <;> rcases psiT_val hR with rfl | rfl <;> first | rfl | exact absurd e (by decide)
    subst hv'
    exact ⟨hrel', hH', ⟨tr, hsp'⟩, fun e => q_keep (h0 e) hk.full, fun e => q_keep (h1 e) hk.full⟩
  · rcases hvals with h | ⟨hlt, R, hR, hex, hvr, hvw⟩
    · exact absurd (by rw [h]) e
    · have hmin : tr ≤ min σ'.vs.vrNew σ'.vs.vwNew := Nat.le_min.mpr ⟨hvr, hvw⟩
      have full_of : ∀ {x w}, Full x w tr R → Full x w (min σ'.vs.vrNew σ'.vs.vwNew) σ'.r := by
        intro x w ⟨hq, ts, hX, hm, hts⟩
        obtain ⟨-, hq', hX'⟩ := hex x hq
        exact ⟨hq', ts, (hX' _).mpr hX, fun p hp => hm p ((hX' p).mp hp), Nat.le_trans hts hmin⟩
      rcases hk3 with rfl | rfl | rfl
      · -- round 0: `tail = 1`, the first `T := 1` (`GA`); the second needs `GB`, which the consumer holds
        rcases hR with ⟨rfl, ⟨hF, hGA⟩ | ⟨-, hGBR⟩⟩ | ⟨rfl, -⟩
        · exact ⟨hrel', hH', fun _ => ⟨tr, hsp'⟩, full_of hF, (hex _ hGA).2.1, fun _ => q_keep (h0 rfl) hk.full⟩
        · have := (hex _ hGBR).1; rw [h0 rfl] at this; exact absurd this (by decide)
        · exact absurd rfl e
      · -- round 1: `tail = 0` after the initial message: all of `B1`
        rcases hR with ⟨rfl, -⟩ | ⟨rfl, ⟨htr0, -⟩ | hF⟩
        · exact absurd rfl e
        · exact absurd htr0 (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
        · exact ⟨hrel', hH', fun _ => ⟨tr, hsp'⟩, full_of hF, q_keep (h1 (by decide)) hk.full,
            fun e => absurd rfl e⟩
      · -- round 2: `tail = 1`, the second `T := 1` (`GB`); the first needs `GA`, which the consumer holds
        rcases hR with ⟨rfl, ⟨-, hGAR⟩ | ⟨hF, hGB⟩⟩ | ⟨rfl, -⟩
        · have := (hex _ hGAR).1; rw [h1 (by decide)] at this; exact absurd this (by decide)
        · exact ⟨hrel', hH', fun e => absurd rfl e, full_of hF, q_keep (h1 (by decide)) hk.full,
            fun _ => (hex _ hGB).2.1⟩
        · exact absurd rfl e

theorem cslot_ne_T {P : SP} (hL : SpscLocs P) (k : Nat) : cslot P k ≠ P.T := by
  unfold cslot; split
  · exact hL.b1_t
  · exact hL.b0_t

theorem cslot_ne_H {P : SP} (hL : SpscLocs P) (k : Nat) : cslot P k ≠ P.H := by
  unfold cslot; split
  · exact hL.b1_h
  · exact hL.b0_h

/-- **VC `movl (%rbx,%rdx,1), %r1Xd`** (the data load of round `k`): `CX`
is kept, and under the clean flag the load returns `cval k` (`read_max`). -/
theorem vcC_data {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ σ' : EStateX} {v : Val} (h : CX P k σ)
    (hs : (EC P tid).step (.load .plain false (cslot P k).addr 4) σ v σ') : CX P k σ' ∧ (σ'.cl → v = cval k) := by
  have hk := loadKeep hs
  have hsl : (⟨(cslot P k).addr, 4⟩ : Loc) = cslot P k := by unfold cslot; split <;> rfl
  rw [hsl] at hk
  obtain ⟨hrel, hH, hsp, hS, hGA, hGB⟩ := h
  refine ⟨⟨by rw [hk.rel]; exact hrel, q_keep hH hk.full,
    fun e => (hsp e).elim fun K h => ⟨K, h.load_other hk (Ne.symm (cslot_ne_T hL k))⟩,
    hS.keep hk.full (min_mono hk.vs.vrNew hk.vs.vwNew), q_keep hGA hk.full, fun e => q_keep (hGB e) hk.full⟩,
    fun hc => ?_⟩
  obtain ⟨ga, hanc, -, hcl, tr, hrd, -⟩ := step_loadFactsT (pl := consPlan P) hs
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
    ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  obtain ⟨hq, ts, hX, hmax, hts⟩ := hS
  have hrd' := hrd.val
  have hwi := hrd.window
  rw [hsl] at hrd' hwi
  exact (read_max E' ht hq hX hmax hrd' hp hwi
    (Nat.le_trans hts (Nat.le_trans (Nat.min_le_left _ _) (le_readBound_vrNew _ _ _ _)))).2

/-- **VC `movl %eax, (%rsi)`** (the `head` store of round `k`): `H := 1`
(rounds 0, 2) is the planned release giving `B0` and `GB` (`psiH`); `H := 0`
(round 1) is pure. Gives `CE (k + 1)` (rounds 0, 1). -/
theorem vcC_storeH {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 0 ∨ k = 1 ∨ k = 2) {σ : EStateX}
    (h : CX P k σ) :
    (EC P tid).ok (.store .plain false P.h 4 (hNew k)) σ ∧
      ∀ b (σ' : EStateX), (EC P tid).step (.store .plain false P.h 4 (hNew k)) σ b σ' →
        (k = 0 → CE P 1 σ') ∧ (k = 1 → CE P 2 σ') := by
  obtain ⟨hrel, hH, hsp, hS, hGA, hGB⟩ := h
  have hwh := cons_whole (P := P) P.H (hNew k)
  have hHg : P.H ∉ (consPlan P).gives P.H (hNew k) := (consPlan_valid hL).not_mem_gives _ _
  have hok : (EC P tid).ok (.store .plain false P.h 4 (hNew k)) σ := by
    refine ⟨⟨rfl, by show 0 < (σ.r.wr P.H).q; rw [hH]; decide, fun hr => ?_, fun hr => ?_⟩,
      by simp [SharedEnv.AccessIn]⟩
    · -- unplanned: round 1, `H := 0`, pure
      show Pred.Pure (σ.g.rel P.H) _
      rw [hrel, relS_H hL]
      rcases hk3 with rfl | rfl | rfl
      · exact absurd hr (by rw [show hNew 0 = 1#128 from rfl, cons_rel_H1]; decide)
      · exact psiH_pure_zero P
      · exact absurd hr (by rw [show hNew 2 = 1#128 from rfl, cons_rel_H1]; decide)
    · -- planned: rounds 0 and 2, `H := 1`, giving `B0` and `GB`
      have hk02 : k = 0 ∨ k = 2 := by
        rcases hk3 with rfl | rfl | rfl
        · exact .inl rfl
        · exact absurd hr (by rw [show hNew 1 = 0#128 from rfl, cons_rel_H0]; decide)
        · exact .inr rfl
      have hv : hNew k = 1#128 := by rcases hk02 with rfl | rfl <;> rfl
      have hsl : cslot P k = P.B0 := by rcases hk02 with rfl | rfl <;> rfl
      have hGB' : (σ.r.wr GB).q = 1 := hGB (by rcases hk02 with rfl | rfl <;> decide)
      refine ⟨.inl rfl, ?_, hHg, ?_⟩
      · show ¬ Pred.Pure (σ.g.rel P.H) _
        rw [hrel, relS_H hL, hv]
        intro hp
        exact absurd (psiH_pure P hp) (by decide)
      intro c g _ hwb
      show (σ.g.rel P.H).P _ _ _ _
      rw [hrel, relS_H hL, Plan.give_of_whole _ hwh, hv, cons_gives_H1]
      rw [hsl] at hS
      obtain ⟨hqS, ts, hX, hm, hts⟩ := hS
      have e1 : P.B0 ∈ [P.B0, GB] := by simp
      have e2 : GB ∈ [P.B0, GB] := by simp
      have hlt := hwb.vwNew
      refine .inl ⟨rfl, by rw [wr_only_mem e1]; exact hqS, fun p hp => ?_, by rw [wr_only_mem e2]; exact hGB'⟩
      rw [wr_only_mem e1] at hp
      have := hm p hp
      have := Nat.min_le_right σ.vs.vrNew σ.vs.vwNew
      simp only [Time, View] at *; omega
  refine ⟨hok, fun b σ' hs => ?_⟩
  have hrel' := rel_store hs
  obtain ⟨c, tw, hanc, -, -, -, -, ⟨Pc, -, hr⟩, -⟩ := step_storeFactsT hs
  have hHq : (σ'.r.wr P.H).q = 1 := by
    rw [hr]; unfold Plan.after
    split
    · rw [Res.addW_q, (consPlan P).keep_wr_self hHg hwh]; exact hH
    · rw [Res.addW_q]; exact hH
  refine ⟨fun e => ?_, fun e => ?_⟩
  · subst e
    have hgT : P.T ∉ (consPlan P).gives P.H (hNew 0) := by
      show P.T ∉ (consPlan P).gives P.H 1#128
      rw [cons_gives_H1]; simp [hL.b0_t.symm]
    have hgA : GA ∉ (consPlan P).gives P.H (hNew 0) := by
      show GA ∉ (consPlan P).gives P.H 1#128
      rw [cons_gives_H1]; simp [ne_ga.symm]
    obtain ⟨K, hsp0⟩ := hsp (by decide)
    exact ⟨by rw [hrel']; exact hrel, hHq, ⟨K, hsp0.store_other hs (Ne.symm hL.h_t) hwh hgT⟩,
      fun e => absurd e (by decide), fun _ => by rw [hr, wr_after_ne ne_ga.symm hwh hgA]; exact hGA⟩
  · subst e
    have hgT : P.T ∉ (consPlan P).gives P.H (hNew 1) := by
      show P.T ∉ (consPlan P).gives P.H 0#128
      rw [cons_gives_H0]; simp
    have hgA : GA ∉ (consPlan P).gives P.H (hNew 1) := by
      show GA ∉ (consPlan P).gives P.H 0#128
      rw [cons_gives_H0]; simp
    obtain ⟨K, hsp1⟩ := hsp (by decide)
    exact ⟨by rw [hrel']; exact hrel, hHq, ⟨K, hsp1.store_other hs (Ne.symm hL.h_t) hwh hgT⟩,
      fun e => absurd e (by decide), fun _ => by rw [hr, wr_after_ne ne_ga.symm hwh hgA]; exact hGA⟩

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.vcP_spin
#print axioms Kraken.Promising.X64.EnvG.SpscX.vcP_storeT
#print axioms Kraken.Promising.X64.EnvG.SpscX.vcC_spin
#print axioms Kraken.Promising.X64.EnvG.SpscX.vcC_data
#print axioms Kraken.Promising.X64.EnvG.SpscX.vcC_storeH
