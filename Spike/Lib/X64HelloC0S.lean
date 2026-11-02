/-
**hello.w's start control at `wc_main`'s start segment** (x86-64; the twin of `Spike/Lib/A64HelloC0S.lean`): hello's
thread 0 starts before the setup block (`X64HelloSrc.hello_start`: `setupStartT 2`), so the start segment's control
is that thread's control `c0S := ⟨setupTerm, [me, u], none⟩`.

At load no register or slot holds `me`'s word, the address of main's control block (`X64WakeLoadT.tcb0`,
`pinned.lo + 8`), so the start places `me` at that immediate (`X64.HelloImms.immsH`, at hello's start term
`setupTerm`); `u` has no words.

- `c0S`, `c0S_term`, `c0S_env`, `c0S_u`: the start control, its term, its environment, its unit.
- `placed_c0S`, `placedSE_c0S`: `c0S` placed at `L0T` at every state, at any layout whose immediates put `me` at
  `tcb0` at `setupTerm` (`hme`; `HelloImms.hme_iRdM` at the root's table).
- `cfacts_c0S`: `CFacts` at `c0S` (no `ret`, no load, store or buffer allocation: a call).

Unlike AArch64, the immediate table `immsH` is `X64HelloImms`'s (not restated here), `c0S` is written out (AArch64
reads it off `HelloPreAsm.helloTh0`, whose closure reaches the AArch64 syntax), `me`'s representation is
`X64.WakeImmsC0.valRep_me`, and the source facts at `c0S` (AArch64's `c0S_ctl`, through `HelloRdCf.start_ctl`)
are left to the x86-64 `RdCf` module.
-/
import Spike.Lib.X64WakeImmsC0

namespace Spike.Lib.X64.HelloPh.C0S

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64WakeT1 (mainTidLbl)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

/-- **hello's start control**: thread 0 of `setupStartT 2`, before the setup block, no hold. -/
def c0S : Spike.Lib.Ctl :=
  ⟨Scc.Sem.SrcSem.setupTerm, [("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]), ("u", .unit, [])], none⟩

theorem c0S_term : c0S.term = Scc.Sem.SrcSem.setupTerm := rfl

theorem c0S_env : c0S.env = [("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]), ("u", .unit, [])] := rfl

theorem c0S_u : TermRun.evalAt c0S.env (.var "u") = some (.unit, []) := rfl

/-- **`c0S` is placed at `L0T`** at every state: `me` at the immediate `tcb0`, `u` of no words (`hme`: the
layout's immediates put `me` there). -/
theorem placed_c0S {Λ : Scc.Sem.Layout} (hme : Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ))
    (s : State) : Placed Λ (L0T Λ) s c0S := by
  refine ⟨fun x k => if x = "me" ∧ k = 0 then some (.imm (tcb0 Λ)) else none, ?_, ?_, ?_⟩
  · intro x t ws hx k wd wp hwd hwp
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      rw [c0S_env] at hx
      simp only [TermRun.lookupE] at hx
      cases hx
      cases hwd
      exact Spike.Lib.X64.WakeImmsC0.valRep_me Λ
    · simp only [hc, ite_false] at hwp
      cases hwp
  · intro x hx t ws hl k hk
    have hfv : exprFv Scc.Sem.SrcSem.setupTerm = ["u", "me"] := by decide
    rw [c0S_term, hfv] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [c0S_env] at hl
      simp [TermRun.lookupE] at hl
      obtain ⟨-, rfl⟩ := hl
      simp at hk
    · rw [c0S_env] at hl
      simp only [TermRun.lookupE] at hl
      cases hl
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      exact ⟨.imm (tcb0 Λ), by simp⟩
  · intro x k n hn
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq, WordPlace.imm.injEq] at hn
      subst hn
      rw [c0S_term, hme]
    · simp only [hc, ite_false] at hn
      cases hn

/-- `placed_c0S` with no frames (`PlacedSE`). -/
theorem placedSE_c0S {Λ : Scc.Sem.Layout} (hme : Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ))
    (s : State) : PlacedSE Λ (L0T Λ) s c0S [] :=
  .inl (PlacedS.ofNil (placed_c0S hme s))

/-- **`c0S`'s consumer facts**: no `ret`, no load or store, no buffer allocation (its term is the setup's call of
`rodata`), placed at every state. -/
theorem cfacts_c0S {Λ : Scc.Sem.Layout} (hme : Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ)) :
    CFacts Λ (L0T Λ) c0S := by
  refine ⟨fun a h => ?_, fun x a e ty w h => ?_, fun x a τ e h => ?_, placed_c0S hme⟩
  · rw [c0S_term] at h; cases h
  · rcases h with h | ⟨b, h⟩ <;> rw [c0S_term] at h <;> cases h
  · rw [c0S_term] at h; cases h

end Spike.Lib.X64.HelloPh.C0S

/-- info: 'Spike.Lib.X64.HelloPh.C0S.placed_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.C0S.placed_c0S

/-- info: 'Spike.Lib.X64.HelloPh.C0S.cfacts_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.C0S.cfacts_c0S
