/-
**hello.w's start control at `wc_main`'s start segment** (AArch64; the twin of
`WakeImmsW` + `WakeC0` + `WakeC0CF` for hello's root): hello's thread 0 starts before the setup block
(`setupStartT 2`, `HelloPreAsm.helloTh0`), so the start segment's control `c0` is that thread's control
`c0S := ⟨setupTerm, [me, u], none⟩` (wake's is main's box control `c0W`, after its tail call; hello's start
reaches `wc_main` only through `scc_rt_main`'s calls, whose source the segment carries: `rodata`'s call by
`StartWcS.rdJH_run`).

At load no register or slot holds `me`'s word, the address of main's control block (`WakeLoadT.tcb0`,
`pinned.lo + 8`), so the start places `me` at that immediate (as wake's `WakeImmsW.immsW`, at hello's start
term `setupTerm`); `u` has no words.

- `immsH Λ0 i0`: the immediate table with `me` at `tcb0 Λ0` at `setupTerm`, elsewhere `i0`; `immsH_start`.
- `c0S`, `c0S_term`, `c0S_u`: the start control, its term, its unit.
- `placed_c0S`, `placedSE_c0S`: `c0S` placed at `L0T` at every state, at any layout whose immediates put
  `me` at `tcb0` at `setupTerm` (`hme`; `immsH_start` at `immsH`).
- `cfacts_c0S`: `CFacts` at `c0S` (no `ret`, no load, store or buffer allocation: a call).
- `c0S_ctl`: `HelloRdCf.start_ctl` at `c0S` (the start segment's `hc0`).
-/
import Spike.Lib.WakeImmsW
import Spike.Lib.A64WakeC0CF
import Spike.Lib.HelloPreAsm
import Spike.Lib.A64HelloRdCf

namespace Spike.Lib.A64.HelloPh.C0S

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

open Classical in
/-- **hello's immediate table** at the placement input `Λ0`: at the setup start's term, word 0 of `me` is
main's control block `Λ0.pinned.lo + 8`; elsewhere the base table `i0`. -/
noncomputable def immsH (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) (e : Expr) (x : String)
    (k : Nat) : Option Nat :=
  if e = Scc.Sem.SrcSem.setupTerm ∧ x = "me" ∧ k = 0 then some (Λ0.pinned.lo + 8) else i0 e x k

/-- At the setup start's term, word 0 of `me` is main's control block. -/
theorem immsH_start (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    immsH Λ0 i0 Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ0) := by
  simp [immsH, tcb0]

/-- **hello's start control**: thread 0 of `setupStartT 2`, before the setup block, no hold. -/
def c0S : Spike.Lib.Ctl := ⟨Spike.Lib.HelloPreAsm.helloTh0.term, Spike.Lib.HelloPreAsm.helloTh0.env, none⟩

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
      exact Spike.Lib.WakeImmsW.valRep_me Λ
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

/-- **`c0S`'s consumer facts**: no `ret`, no load or store, no buffer allocation (its term is the setup's
call of `rodata`), placed at every state. -/
theorem cfacts_c0S {Λ : Scc.Sem.Layout} (hme : Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ)) :
    CFacts Λ (L0T Λ) c0S := by
  refine ⟨fun a h => ?_, fun x a e ty w h => ?_, fun x a τ e h => ?_, placed_c0S hme⟩
  · rw [c0S_term] at h; cases h
  · rcases h with h | ⟨b, h⟩ <;> rw [c0S_term] at h <;> cases h
  · rw [c0S_term] at h; cases h

/-- **`c0S`'s source facts** (the start segment's `hc0`): not a `ret`, its runs well formed at no frame. -/
theorem c0S_ctl :
    (∀ a, c0S.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf Spike.Lib.HelloSrc.helloSrc c0S [] :=
  Spike.Lib.HelloRdCf.start_ctl c0S.env

end Spike.Lib.A64.HelloPh.C0S

/-- info: 'Spike.Lib.A64.HelloPh.C0S.immsH_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.C0S.immsH_start

/-- info: 'Spike.Lib.A64.HelloPh.C0S.placed_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.C0S.placed_c0S

/-- info: 'Spike.Lib.A64.HelloPh.C0S.placedSE_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.C0S.placedSE_c0S

/-- info: 'Spike.Lib.A64.HelloPh.C0S.cfacts_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.C0S.cfacts_c0S

/-- info: 'Spike.Lib.A64.HelloPh.C0S.c0S_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.C0S.c0S_ctl
