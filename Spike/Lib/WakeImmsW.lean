/-
**wake's immediate table with main's `ThreadId` at the start** (AArch64): the analogue of hello1's `LowerNode.imms2Me` for wake. Thread
0 starts at `tidStartT 2`'s term `main(me)` (`wakeTh0`). At load no register
or slot holds `me`'s word, which is the address of main's control block
(`WakeLoadT.tcb0`, `pinned.lo + 8`), so the start places `me` at that
immediate. Every other key is a base table `i0` (the certificate's, e.g.
`SccCode.wakeImms`; fixed by the root).

- `startT`: the start's term; `immsW Λ0 i0`: the table at the placement
  input `Λ0` (whose pinned region is the runtime layout's, `ofPlaceW` only
  replacing `imms`);
- `immsW_start`: at the start's term, word 0 of `me` is `tcb0`;
  `immsW_of_ne`: elsewhere it is `i0`;
- `placedSE_start`, `placedSE_startW` (the non-vacuity check for `WakeLoadT.L0T`): at any
  layout whose immediates are `immsW Λ0 i0` and whose pinned region is
  `Λ0`'s, the start's control is `PlacedSE` at `L0T` at every state (`me`
  at `.imm tcb0`, represented since `L0T` puts `mainTidLbl 2` at `tcb0`).

The root must fix `i := immsW Λ0 i0` (at Λe) for `placedSE_start` to
apply.
-/
import Spike.Lib.WakeLoadT
import Spike.Lib.A64PlacedSE
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeImmsW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePreAsm Spike.Lib.WakeLoadT
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

/-- **The start's term**: `main(me)` (`tidStartT`'s thread 0). -/
def startT : Expr := .tail "main" [] (.var "me")

theorem wakeTh0_term : wakeTh0.term = startT := rfl

open Classical in
/-- **wake's immediate table** at the placement input `Λ0`: at the start's
term, word 0 of `me` is main's control block `Λ0.pinned.lo + 8`; elsewhere
the base table `i0`. -/
noncomputable def immsW (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) (e : Expr) (x : String) (k : Nat) : Option Nat :=
  if e = startT ∧ x = "me" ∧ k = 0 then some (Λ0.pinned.lo + 8) else i0 e x k

/-- At the start's term, word 0 of `me` is main's control block. -/
theorem immsW_start (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    immsW Λ0 i0 startT "me" 0 = some (tcb0 Λ0) := by
  simp [immsW, tcb0]

/-- **Elsewhere it is the base table.** -/
theorem immsW_of_ne {Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat} {e : Expr} {x : String} {k : Nat} (h : ¬ (e = startT ∧ x = "me" ∧ k = 0)) :
    immsW Λ0 i0 e x k = i0 e x k := by
  simp only [immsW, h, ite_false]

/-- `me`'s word at the start is represented by `tcb0` at `L0T`. -/
theorem valRep_me (Λ : Scc.Sem.Layout) : ValRep (L0T Λ) (.loc ⟨mainTidLbl 2, 0⟩ 0) (tcb0 Λ) :=
  ⟨by decide, tcb0 Λ, by simp [wordAddr, L0T, Spike.Lib.A64ConsumerA.upd], by simp⟩

/-- **The start's control is placed at `L0T`** at every state (non-vacuity
of `L0T`): `me` at the immediate `tcb0`, at any layout with `immsW Λ0` as
its immediates and `Λ0`'s pinned region. -/
theorem placedSE_start {Λ Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat} (hi : Λ.imms = immsW Λ0 i0) (hpin : Λ.pinned = Λ0.pinned)
    (s : State) : PlacedSE Λ (L0T Λ) s ⟨wakeTh0.term, wakeTh0.env, none⟩ [] := by
  refine .inl (PlacedS.ofNil ⟨fun x k => if x = "me" ∧ k = 0 then some (.imm (tcb0 Λ)) else none, ?_, ?_, ?_⟩)
  · intro x t ws hx k wd wp hwd hwp
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      simp only [wakeTh0, tidStartT, TermRun.lookupE] at hx
      cases hx
      cases hwd
      exact valRep_me Λ
    · simp only [hc, ite_false] at hwp
      cases hwp
  · intro x hx t ws hl k hk
    have hfv : exprFv startT = ["me"] := by decide
    rw [show (⟨wakeTh0.term, wakeTh0.env, none⟩ : Ctl).term = startT from rfl, hfv] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    simp only [wakeTh0, tidStartT, TermRun.lookupE] at hl
    cases hl
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    exact ⟨.imm (tcb0 Λ), by simp⟩
  · intro x k n hn
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq, WordPlace.imm.injEq] at hn
      subst hn
      rw [hi, show (⟨wakeTh0.term, wakeTh0.env, none⟩ : Ctl).term = startT from rfl, immsW_start, tcb0, tcb0, hpin]
    · simp only [hc, ite_false] at hn
      cases hn

/-- **At the runtime's layout with `i := immsW Λ0 i0`** the start's control
is placed at `L0T` at every state. -/
theorem placedSE_startW {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i0 : Expr → String → Nat → Option Nat) (s : State) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (immsW Λ0 i0)).Λ
    PlacedSE Λ (L0T Λ) s ⟨wakeTh0.term, wakeTh0.env, none⟩ [] :=
  placedSE_start rfl rfl s

end Spike.Lib.WakeImmsW

/-- info: 'Spike.Lib.WakeImmsW.placedSE_startW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeImmsW.placedSE_startW
