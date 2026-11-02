/-
**The control facts at `wc_rodata`'s heap abort, discharged** (x86-64; the twin of
`Spike/Lib/A64HelloHabCtlRdI.lean`, `HabCtlRd.HabCtlRdH`'s instance, the twin of `WakePh.HAbStubK.hctl_c0`):
below a call invariant `J1` whose controls are `rodata`'s buffer allocation `rdCN`, the allocator's full exit holds
the counter at a count `o` crossing the cells (`Jfull`; `rdCN`'s count `2 < 2^28`), so its control is `rdCN`
holding `o`: it runs well under the setup call's frame (`X64HelloRdCf.hcf_frH`), it is placed where `rdCN` is,
and the heap abort's obligation (`HeapAbortOblA`) holds, `rdCN` being `HeapReady` at `o` (three units: two lanes
and the header).

The placement is asked at every state (`HabCtlRdH`, as `HabCtlH`): `placedS_rdCN` gives it with every word at an
immediate, `rdCN`'s `m` at `eB` (`helloImms`'s `helloImm_t2`) and the frame's `me` at `tcb0` at
`SrcCalls.setupCont` (the frame still reads `me`). Hypothesis: the root's tables have no entry at `setupCont`'s
`me` yet (its soundness: `me`'s word is main's `ThreadId` box at `tcb0`, `WakeImmsC0.valRep_me`).

- `placedS_rdCN`: `rdCN` under `frH c0S.env` placed at `L0T` at every state, from the two immediates.
- `habCtlRdH_rdCN`: the instance.

Unlike AArch64, `HabCtlRdH` takes `wc_rodata`'s region `R` (x86-64's `rX .x13` reads `%rbp` against it); the
instance holds at every `R`, the abort node not reading it. The source side is `X64HelloRodataSrc`,
`X64HelloSrc.helloSrc` (the x86-64 program's).
-/
import Spike.Lib.X64HelloHabCtlRd
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64HelloRdCf
import Spike.Lib.X64WakeWcWf

namespace Spike.Lib.X64.HelloPh.HabCtlRdI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib (Arena HeapAbortOblA Region)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64HelloRdCf (frH)
open Spike.Lib.X64HelloRodataSrc (rdCN eB eW0)
open Spike.Lib.Hello1RodataSrc (τ8)
open Spike.Lib.X64.HelloPh.C0S (c0S c0S_env)
open Spike.Lib.X64.HelloPh.HabCtlRd (HabCtlRdH)

/-- **`rdCN` under the setup call's frame is placed at `L0T`** at every state, every word at an immediate:
`rdCN`'s `m` (word `2`) at `eB` (`hm`) and the frame's `me` (main's `ThreadId` box) at `tcb0` at
`SrcCalls.setupCont` (`hme`). -/
theorem placedS_rdCN {Λ : Scc.Sem.Layout} (hm : Λ.imms eB "m" 0 = some 2)
    (hme : Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ)) (s : State) :
    PlacedS Λ (L0T Λ) s rdCN [frH c0S.env] := by
  refine ⟨fun d x k => if d = 0 ∧ x = "m" ∧ k = 0 then some (.imm 2)
    else if d = 1 ∧ x = "me" ∧ k = 0 then some (.imm (tcb0 Λ)) else none, ?_, ?_, ?_⟩
  · intro d env hd x ty ws hx k wd wp hwd hwp
    rcases d with _ | _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      by_cases hc : x = "m" ∧ k = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [and_self, ite_true, Option.some.injEq] at hwp
        subst hwp
        simp [rdCN, Spike.Lib.Hello1RodataSrc.envN, TermRun.lookupE] at hx
        obtain ⟨-, rfl⟩ := hx
        cases hwd
        exact ⟨by decide, rfl⟩
      · simp [hc] at hwp
    · simp only [envsOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hd
      subst hd
      by_cases hc : x = "me" ∧ k = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp at hwp
        subst hwp
        rw [c0S_env] at hx
        simp only [TermRun.lookupE] at hx
        cases hx
        cases hwd
        exact Spike.Lib.X64.WakeImmsC0.valRep_me Λ
      · simp [hc] at hwp
    · simp [envsOf] at hd
  · intro d env xs hd hxs x hx ty ws hl k hk
    rcases d with _ | _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      simp only [fvOf, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hd hxs
      have hfv : exprFv rdCN.term = ["m", "m"] := by decide
      rw [hfv] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      subst hx
      simp [rdCN, Spike.Lib.Hello1RodataSrc.envN, TermRun.lookupE] at hl
      obtain ⟨-, rfl⟩ := hl
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      exact ⟨.imm 2, by simp⟩
    · simp only [envsOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hd
      simp only [fvOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hxs
      subst hd hxs
      have hfv : (exprFv (frH c0S.env).body).filter (· != (frH c0S.env).x) = ["me"] := by decide
      rw [hfv] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      rw [c0S_env] at hl
      simp only [TermRun.lookupE] at hl
      cases hl
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      exact ⟨.imm (tcb0 Λ), by simp⟩
    · simp [envsOf] at hd
  · intro d e x k n he hn
    rcases d with _ | _ | d
    · simp only [termsOf, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      by_cases hc : x = "m" ∧ k = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [and_self, ite_true, Option.some.injEq, WordPlace.imm.injEq] at hn
        subst hn
        exact hm
      · simp [hc] at hn
    · simp only [termsOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at he
      subst he
      by_cases hc : x = "me" ∧ k = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp at hn
        subst hn
        exact hme
      · simp [hc] at hn
    · simp [termsOf] at he

/-- **`HabCtlRdH` below `rdCN`** (`HAbStubK.hctl_c0W`'s twin): at `rX .abort` below a call invariant whose
controls are `rdCN` (`hJ1`), the allocation's count is `2`, so the full exit is the counter's crossing (`Jfull`'s
second disjunct, `o ≤ cells < o + 3`, the memory side's units `hu`): the control `rdCN` holding `o` runs well at
`[frH env]` (`HelloRdCf.hcf_frH`), is placed where `rdCN` is (`hpl`, e.g. `placedS_rdCN`), and is `HeapReady` at
the held count (the memory side's counter and cells the arena's, `hctr`, `hcells`). -/
theorem habCtlRdH_rdCN {ms : Spike.Lib.MemSide isa} {lab : String → Int64} {Λ : Scc.Sem.Layout}
    {ar : Arena} {env : TermRun.Env} {R : Region} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells)
    (hu : ms.units 2 τ8 = 3) (hpl : ∀ s, PlacedSE Λ (L0T Λ) s rdCN [frH env]) :
    HabCtlRdH ms lab Spike.Lib.X64HelloSrc.helloSrc Λ (L0T Λ) R ar [frH env] J1 := by
  rintro σ c0 ⟨-, -, q, hfull, σe, hJ⟩
  have hq : q.1.c0 = rdCN := hJ1 σe _ hJ
  obtain ⟨h1, h2, h3, -, -⟩ := Spike.Lib.X64HelloRodataSrc.rdCN_newBuf
  have ht := q.2.term
  have hv := q.2.ev
  have hn := q.2.num
  rw [hq, h1] at ht
  simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
  obtain ⟨-, ⟨ha, hτ⟩, -⟩ := ht
  rw [hq, ← ha, h2] at hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  rw [← hv.2, h3] at hn
  simp only [Option.some.injEq] at hn
  rcases hfull with ⟨-, hbig⟩ | ⟨o, rfl, -, hlt⟩
  · rw [← hn] at hbig; exact absurd hbig (by decide)
  rw [← hn, ← hτ, hu] at hlt
  rw [hq]
  refine ⟨Spike.Lib.X64HelloRdCf.hcf_frH (Spike.Lib.X64HelloRdCf.rd_terms default 0 default default).2.1,
    fun s => Spike.Lib.X64.WakePh.WcWf.PlacedSE.hold.2 (hpl s), fun old h => ?_⟩
  obtain ⟨hle, hw⟩ := h (.inl ⟨"b", .var "m", τ8, eW0, rfl⟩)
  have he := hw _ (by rw [← hctr]; rfl)
  have ho : o.toNat = old := by simpa [TermRun.cst, Promises.TVal.mk0] using he
  exact .inl ⟨"b", .var "m", τ8, eW0, .intS (.lit 2), [TermRun.cst (.num 2)], 2, [.one], rfl, rfl, rfl, rfl, hle,
    by
      have h1 : TermRun.nWords [TermRun.Acc.one] = 1 := by decide
      rw [h1, ← hcells, ← ho]; omega⟩

/-- **Not vacuous**: the instance's placement premise at the frame `frH c0S.env` from the two immediates. -/
example {ms : Spike.Lib.MemSide isa} {lab : String → Int64} {Λ : Scc.Sem.Layout} {ar : Arena} {R : Region}
    {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} (hJ1 : ∀ σ c, J1 σ c → c = rdCN)
    (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells) (hu : ms.units 2 τ8 = 3)
    (hm : Λ.imms eB "m" 0 = some 2) (hme : Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ)) :
    HabCtlRdH ms lab Spike.Lib.X64HelloSrc.helloSrc Λ (L0T Λ) R ar [frH c0S.env] J1 :=
  habCtlRdH_rdCN hJ1 hctr hcells hu fun s => .inl (placedS_rdCN hm hme s)

end Spike.Lib.X64.HelloPh.HabCtlRdI

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlRdI.placedS_rdCN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlRdI.placedS_rdCN

/--
info: 'Spike.Lib.X64.HelloPh.HabCtlRdI.habCtlRdH_rdCN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlRdI.habCtlRdH_rdCN
