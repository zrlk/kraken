/-
**wake's immediate table with main's `ThreadId` at the box** (AArch64):
`WakeImmsW.immsW` plus `me` at main's control block (`WakeLoadT.tcb0`) at
the box's term `wakeImm_t1` (`WakeC0.c0W`'s), where the certificate's table
has only `z`. `me`'s word there is the same locative as at the start
(main's `ThreadId` box at `tcb0` under `L0T`), so the immediate represents
it at every state.

- `immsW2 Λ0 i0`: the table; `immsW2_c0` its `me` entry, `immsW2_of_ne`
  elsewhere `immsW`;
- `placedSE_c0W`: at any layout with `immsW2 Λ0 i0` as its immediates, `i0`
  keeping `z` at `0` at the box, and `Λ0`'s pinned region, `c0W` is
  `PlacedSE` at `L0T` at every state (`z` at `.imm 0`, `me` at `.imm tcb0`);
- `placedSE_c0WW`: the same at `ofPlaceW` with `i := immsW2 Λ0 wakeImms`;
- `placedSE_start2`, `placedSE_start2W`: the start's control stays placed at `immsW2`
  (`WakeImmsW.placedSE_start` unchanged; the new entry is at another term).

The table is keyed by term, not by thread, so the entry admits `.imm tcb0`
for `me` at any frame at `wakeImm_t1`. That is not a soundness gap: the
table only permits immediates (`Components.env_imm`), while
`Components.env_rep` checks, at every state and every frame,
`WordPlaceRep … (.imm n) w = ValRep lbl w n`. A frame whose `me` is not
main's `ThreadId` box at `tcb0` therefore fails to be placed at the
immediate; it is not wrongly placed. Moreover, only `main` reaches
`wakeImm_t1` (`WakePreA.main_body`); `worker` and `waitLoop` have
different bodies, and `main` runs only in thread 0, with `me` from
`tidStartT`.
-/
import Spike.Lib.WakeImmsW
import Spike.Lib.A64WakeC0

namespace Spike.Lib.WakeImmsC0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeLoadT
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.WakeC0 (c0W)

open Classical in
/-- **The base table with `me` at the box**: `i0`, and word 0 of `me` at
`tcb0 Λ0` at the box's term. -/
noncomputable def meAt (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) (e : Expr) (x : String)
    (k : Nat) : Option Nat :=
  if e = SccCode.wakeImm_t1 ∧ x = "me" ∧ k = 0 then some (tcb0 Λ0) else i0 e x k

/-- **The table with `me` at the start and at the box**: `WakeImmsW.immsW`
over `meAt`, so `WakeImmsW.placedSE_start` holds at it unchanged. -/
noncomputable abbrev immsW2 (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    Expr → String → Nat → Option Nat :=
  WakeImmsW.immsW Λ0 (meAt Λ0 i0)

/-- The box's term is not the start's. -/
theorem t1_ne_startT : SccCode.wakeImm_t1 ≠ WakeImmsW.startT := by
  simp [SccCode.wakeImm_t1, WakeImmsW.startT]

theorem immsW2_c0 (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    immsW2 Λ0 i0 SccCode.wakeImm_t1 "me" 0 = some (tcb0 Λ0) := by
  rw [immsW2, WakeImmsW.immsW_of_ne (by simp [t1_ne_startT])]; simp [meAt]

theorem immsW2_of_ne {Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat} {e : Expr} {x : String}
    {k : Nat} (h0 : ¬ (e = WakeImmsW.startT ∧ x = "me" ∧ k = 0))
    (h : ¬ (e = SccCode.wakeImm_t1 ∧ x = "me" ∧ k = 0)) : immsW2 Λ0 i0 e x k = i0 e x k := by
  rw [immsW2, WakeImmsW.immsW_of_ne h0]; simp only [meAt, h, ite_false]

/-- **The start's control is placed at `L0T`** at `immsW2` too (`me` at the
start's immediate; the box's entry is at another term). -/
theorem placedSE_start2 {Λ Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat}
    (hi : Λ.imms = immsW2 Λ0 i0) (hpin : Λ.pinned = Λ0.pinned) (s : State) :
    PlacedSE Λ (L0T Λ) s ⟨WakePreAsm.wakeTh0.term, WakePreAsm.wakeTh0.env, none⟩ [] :=
  WakeImmsW.placedSE_start hi hpin s

/-- **`c0W` is placed at `L0T`** at every state: `z` at the immediate `0`
(`i0`'s), `me` at the immediate `tcb0`. -/
theorem placedSE_c0W {Λ Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat}
    (hi : Λ.imms = immsW2 Λ0 i0) (hpin : Λ.pinned = Λ0.pinned) (hz : i0 SccCode.wakeImm_t1 "z" 0 = some 0)
    (s : State) : PlacedSE Λ (L0T Λ) s c0W [] := by
  have hlz : List.lookup "z" [("z", [WordPlace.imm 0]), ("me", [WordPlace.imm (tcb0 Λ)])] =
      some [(.imm 0 : WordPlace (machine (kernel 1)).I.RegId)] := rfl
  have hlm : List.lookup "me" [("z", [WordPlace.imm 0]), ("me", [WordPlace.imm (tcb0 Λ)])] =
      some [(.imm (tcb0 Λ) : WordPlace (machine (kernel 1)).I.RegId)] := rfl
  have henv : ∀ x ty ws, TermRun.lookupE c0W.env x = some (ty, ws) →
      (x = "z" ∧ ws = [TermRun.cst (.num 0)]) ∨ (x = "me" ∧ ws = [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    intro x ty ws hl
    by_cases hz' : x = "z"
    · subst hz'; simp [c0W, TermRun.lookupE] at hl; exact .inl ⟨rfl, hl.2.symm⟩
    by_cases hm : x = "me"
    · subst hm; simp [c0W, TermRun.lookupE] at hl; exact .inr ⟨rfl, hl.2.symm⟩
    have h1 : ("z" == x) = false := by simpa [beq_iff_eq] using Ne.symm hz'
    have h2 : ("me" == x) = false := by simpa [beq_iff_eq] using Ne.symm hm
    simp [c0W, TermRun.lookupE, List.find?, h1, h2] at hl
  refine WakeSrcCtl.placedSE_of_tbl [("z", [.imm 0]), ("me", [.imm (tcb0 Λ)])] ?_ ?_ ?_
  · intro x _ ty ws hl
    rcases henv x ty ws hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hlz, by simp⟩
    · exact ⟨_, hlm, by simp⟩
  · intro x pls ty ws ht hl k wp wd hwp hwd
    rcases henv x ty ws hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hlz] at ht; cases ht
      rcases k with _ | k <;> simp at hwp hwd
      subst hwp hwd; exact ⟨by decide, rfl⟩
    · rw [hlm] at ht; cases ht
      rcases k with _ | k <;> simp at hwp hwd
      subst hwp hwd; exact WakeImmsW.valRep_me Λ
  · intro x pls k n ht hn
    rw [show c0W.term = SccCode.wakeImm_t1 from rfl, hi]
    by_cases hz' : x = "z"
    · subst hz'
      rw [hlz] at ht; cases ht
      rcases k with _ | k <;> simp at hn
      subst hn
      rw [immsW2_of_ne (by simp [t1_ne_startT]) (by simp), hz]
    by_cases hm : x = "me"
    · subst hm
      rw [hlm] at ht; cases ht
      rcases k with _ | k <;> simp at hn
      subst hn
      rw [immsW2_c0, tcb0, tcb0, hpin]
    have h1 : (x == "z") = false := by simpa [beq_iff_eq] using hz'
    have h2 : (x == "me") = false := by simpa [beq_iff_eq] using hm
    simp [List.lookup, h1, h2] at ht

/-- **At the runtime's layout with `i := immsW2 Λ0 wakeImms`**, `c0W` is
placed at `L0T` at every state. -/
theorem placedSE_c0WW {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (s : State) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (immsW2 Λ0 SccCode.wakeImms)).Λ
    PlacedSE Λ (L0T Λ) s c0W [] :=
  placedSE_c0W rfl rfl (by simp [SccCode.wakeImms]) s

/-- **At the runtime's layout with `i := immsW2 Λ0 wakeImms`**, the start's
control is placed at `L0T` at every state. -/
theorem placedSE_start2W {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (s : State) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (immsW2 Λ0 SccCode.wakeImms)).Λ
    PlacedSE Λ (L0T Λ) s ⟨WakePreAsm.wakeTh0.term, WakePreAsm.wakeTh0.env, none⟩ [] :=
  WakeImmsW.placedSE_startW hp (meAt Λ0 SccCode.wakeImms) s

end Spike.Lib.WakeImmsC0

/-- info: 'Spike.Lib.WakeImmsC0.placedSE_c0WW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeImmsC0.placedSE_c0WW
