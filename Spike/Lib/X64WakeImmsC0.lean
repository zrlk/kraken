/-
**The start's and the box's controls placed at `L0T`** (x86-64): the
placement rows of wake's start, at the immediate table
`X64.WakeImms.immsW2 Λ0 i0` (main's `ThreadId` word `me` at the immediate
`tcb0 Λ0` at the start's term and at the box's term `wakeImm_t1`).

- `valRep_me`: `me`'s word is represented by `tcb0` at `L0T`.
- `placedSE_start`, `placedSE_startW`: the start's control
  (`Ctl.of wakeTh0`, `me` at `.imm tcb0`) is `PlacedSE` at `L0T` at every
  state (`hplS`).
- `placedSE_c0W`, `placedSE_c0WW`: `c0W` is `PlacedSE` at `L0T` at every
  state (`z` at `.imm 0`, `me` at `.imm tcb0`; `hpl0`).
- `PlacedS.head`: a placed frame stack's current frame is `Placed`.
- `cfacts_c0W`, `cfacts_c0WW`: `c0W`'s `CFacts` at `L0T` (`hC0`).

The `…W` forms are at `RuntimeLayout.ofPlaceWX hp (X64.WakeImms.iW Λ0)`:
the root must fix its immediate table to `iW Λ0`.

x86-64 twin of `Spike.Lib.WakeImmsW.valRep_me`/`placedSE_start(W)`,
`Spike.Lib.WakeImmsC0.placedSE_c0W(W)`/`placedSE_start2W` and
`Spike.Lib.A64.WakeC0CF` (same proofs).

**Unlike AArch64**:
- the table's definitions are `X64.WakeImms`'s (data only there), and the
  start's control is stated as `Ctl.of wakeTh0` (`StartH0B.cS`; the same
  control as AArch64's `⟨wakeTh0.term, wakeTh0.env, none⟩`);
- the runtime layout is `ofPlaceWX` (A64 `ofPlaceW`), the placement
  `X64.WakeSrcCtl.placedSE_of_tbl`, the consumer x86-64's;
- `immsW2` at the start's `me` is taken from `X64.WakeImms.immsW_start`
  (the outer `immsW` layer), so no `placedSE_start2` restatement is needed:
  `placedSE_start` is already at `immsW2 Λ0 i0 = immsW Λ0 (meAt Λ0 i0)`.
-/
import Spike.Lib.X64WakeImms
import Spike.Lib.X64WakeLoadT
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64WakeC0
import Spike.Lib.X64SegInst
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64.WakeImmsC0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Ctl PlaceWX)
open Spike.Lib.X64WakeT1 (mainTidLbl)
open Spike.Lib.X64WakeT1 (tidStartT)
open Spike.Lib.X64WakePreAsm (wakeTh0)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64.WakeImms (startT immsW immsW2 meAt iW t1_ne_startT immsW_start immsW2_c0)
open Spike.Lib.X64.WakeC0 (c0W c0W_term)

/-- The start's term is `startT`. -/
theorem wakeTh0_term : wakeTh0.term = startT := rfl

/-- At the box's term the two tables agree with the base one away from `me`. -/
theorem immsW2_of_ne {Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat} {e : Expr} {x : String}
    {k : Nat} (h0 : ¬ (e = startT ∧ x = "me" ∧ k = 0))
    (h : ¬ (e = SccCode.wakeImm_t1 ∧ x = "me" ∧ k = 0)) : immsW2 Λ0 i0 e x k = i0 e x k := by
  simp only [immsW2, immsW, meAt, h0, h, ite_false]

/-- `me`'s word at the start is represented by `tcb0` at `L0T`. -/
theorem valRep_me (Λ : Scc.Sem.Layout) : ValRep (L0T Λ) (.loc ⟨mainTidLbl 2, 0⟩ 0) (tcb0 Λ) :=
  ⟨by decide, tcb0 Λ, by simp [wordAddr, L0T, Spike.Lib.X64ConsumerA.upd], by simp⟩

/-- **The start's control is placed at `L0T`** at every state (`me` at the
immediate `tcb0`), at any layout with `immsW Λ0 i0` as its immediates and
`Λ0`'s pinned region. -/
theorem placedSE_start {Λ Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat}
    (hi : Λ.imms = immsW Λ0 i0) (hpin : Λ.pinned = Λ0.pinned) (s : State) :
    PlacedSE Λ (L0T Λ) s (Ctl.of wakeTh0) [] := by
  refine .inl (PlacedS.ofNil ⟨fun x k => if x = "me" ∧ k = 0 then some (.imm (tcb0 Λ)) else none, ?_, ?_, ?_⟩)
  · intro x t ws hx k wd wp hwd hwp
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      simp only [Ctl.of, wakeTh0, tidStartT, TermRun.lookupE] at hx
      cases hx
      cases hwd
      exact valRep_me Λ
    · simp only [hc, ite_false] at hwp
      cases hwp
  · intro x hx t ws hl k hk
    have hfv : exprFv startT = ["me"] := by decide
    rw [show (Ctl.of wakeTh0).term = startT from rfl, hfv] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    simp only [Ctl.of, wakeTh0, tidStartT, TermRun.lookupE] at hl
    cases hl
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    exact ⟨.imm (tcb0 Λ), by simp⟩
  · intro x k n hn
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq, WordPlace.imm.injEq] at hn
      subst hn
      rw [hi, show (Ctl.of wakeTh0).term = startT from rfl, immsW_start, tcb0,
        Spike.Lib.X64.WakeImms.tcb0, hpin]
    · simp only [hc, ite_false] at hn
      cases hn

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
  refine Spike.Lib.X64.WakeSrcCtl.placedSE_of_tbl [("z", [.imm 0]), ("me", [.imm (tcb0 Λ)])] ?_ ?_ ?_
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
      subst hwp hwd; exact valRep_me Λ
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
      rw [immsW2_c0, tcb0, Spike.Lib.X64.WakeImms.tcb0, hpin]
    have h1 : (x == "z") = false := by simpa [beq_iff_eq] using hz'
    have h2 : (x == "me") = false := by simpa [beq_iff_eq] using hm
    simp [List.lookup, h1, h2] at ht

/-- **The current frame of a placed frame stack is placed** (`envm 0`). -/
theorem PlacedS.head {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PlacedS Λ lbl s c fs) : Placed Λ lbl s c := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm 0, fun x ty ws hl k wd wp hwd hwp => hrep 0 c.env (by simp [envsOf]) x ty ws hl k wd wp hwd hwp,
    fun x hx ty ws hl k hk => htot 0 c.env _ (by simp [envsOf]) (by simp [fvOf]) x hx ty ws hl k hk,
    fun x k n h => himm 0 c.term x k n (by simp [termsOf]) h⟩

/-- **`c0W`'s source facts** at `immsW2` (`hi`), `Λ0`'s pinned region
(`hpin`), `z` at `0` at the box (`hz`): no `ret`, no load or store, no
buffer allocation, placed at every state. -/
theorem cfacts_c0W {Λ Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat}
    (hi : Λ.imms = immsW2 Λ0 i0) (hpin : Λ.pinned = Λ0.pinned)
    (hz : i0 SccCode.wakeImm_t1 "z" 0 = some 0) : CFacts Λ (L0T Λ) c0W := by
  refine ⟨fun a h => ?_, fun x a e ty w h => ?_, fun x a τ e h => ?_, fun s => ?_⟩
  · rw [c0W_term] at h; cases h
  · rcases h with h | ⟨b, h⟩ <;> rw [c0W_term] at h <;> cases h
  · rw [c0W_term] at h; cases h
  · rcases placedSE_c0W hi hpin hz s with h | ⟨h, -⟩
    · exact PlacedS.head h
    · exfalso
      rcases h with h | h <;> rw [c0W_term] at h
      · simp [Scc.Sem.externModelTerms, Scc.Sem.modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
          Scc.Frontend.printLPubBody, Scc.Frontend.printAdv, Scc.Frontend.printNext] at h
      · simp [Scc.Sem.exprFv] at h
        have h1 := h.1
        simp only [Scc.Sem.opVars, Scc.Sem.opAts] at h1
        simp [Scc.Sem.atVars] at h1

/-! ## At the runtime's layout with `i := iW Λ0` -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`hplS`**: the start's control is placed at `L0T` at every state. -/
theorem placedSE_startW (hp : PlaceWX pcfg Λ0 o) (s : State) :
    let Λ := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iW Λ0)).Λ
    PlacedSE Λ (L0T Λ) s (Ctl.of wakeTh0) [] :=
  placedSE_start rfl rfl s

/-- **`hpl0`**: `c0W` is placed at `L0T` at every state. -/
theorem placedSE_c0WW (hp : PlaceWX pcfg Λ0 o) (s : State) :
    let Λ := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iW Λ0)).Λ
    PlacedSE Λ (L0T Λ) s c0W [] :=
  placedSE_c0W rfl rfl (by simp [SccCode.wakeImms]) s

/-- **`hC0`**: `c0W`'s source facts at `L0T`. -/
theorem cfacts_c0WW (hp : PlaceWX pcfg Λ0 o) :
    let Λ := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iW Λ0)).Λ
    CFacts Λ (L0T Λ) c0W :=
  cfacts_c0W rfl rfl (by simp [SccCode.wakeImms])

end Spike.Lib.X64.WakeImmsC0

/-- info: 'Spike.Lib.X64.WakeImmsC0.wakeTh0_term' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.wakeTh0_term

/-- info: 'Spike.Lib.X64.WakeImmsC0.immsW2_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.immsW2_of_ne

/-- info: 'Spike.Lib.X64.WakeImmsC0.valRep_me' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.valRep_me

/-- info: 'Spike.Lib.X64.WakeImmsC0.placedSE_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.placedSE_start

/-- info: 'Spike.Lib.X64.WakeImmsC0.placedSE_c0W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.placedSE_c0W

/-- info: 'Spike.Lib.X64.WakeImmsC0.PlacedS.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.PlacedS.head

/-- info: 'Spike.Lib.X64.WakeImmsC0.cfacts_c0W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.cfacts_c0W

/-- info: 'Spike.Lib.X64.WakeImmsC0.placedSE_startW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.placedSE_startW

/-- info: 'Spike.Lib.X64.WakeImmsC0.placedSE_c0WW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.placedSE_c0WW

/-- info: 'Spike.Lib.X64.WakeImmsC0.cfacts_c0WW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeImmsC0.cfacts_c0WW
