/-
**The source hooks the consumer accepts** (`HookOK P p`): no extern step
(`SrcHooks.none`), or WeakCore's extern step (`SrcOutProto.UsesWc`) with no
exit event in the hook's event list at any reachable configuration. The
consumers (`Spike/Lib/*Consumer*.lean`) take `HookOK P p` where they took
`P.hooks = SrcHooks.none`: their source runs are machine steps of thread 0,
which keep the hook's event list, so only `main`'s exit labels them.

- `HookOK.none`, `HookOK.wc`: the two hooks;
- `HookOK.trace_set`: the hook's event list ignores the threads;
- `HookOK.trace_stepBy`: a machine step keeps the hook's event list;
- `HookOK.noExit`: no exit event in the hook's event list at a reachable
  configuration;
- `HookOK.cutAtExit_of_noExit`, `HookOK.cutAtExit_append_of_noExit`:
  `cutAtExit` keeps a list with no exit event, and anything appended to it
  is cut on its own.
-/
import Scc.Sem.SrcOutProto
import Spike.Lib.Src

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem Ev)
open Scc.Sem.SrcSem (cutAtExit)

/-- **The source hooks the consumer accepts**: none, or WeakCore's extern
step whose event list has no exit event at a reachable configuration (`main`'s
exit, if any, is then the only exit of the observable trace). -/
def HookOK (P : SrcSem.SrcParams) (p : Prog) : Prop :=
  P.hooks = SrcSem.SrcHooks.none ∨
    (Scc.Sem.SrcOutProto.UsesWc P p ∧
      ∀ tr s, (SrcSem.source P p).Reach tr s → ∀ x, Ev.exit x ∉ P.hooks.trace s)

namespace HookOK

variable {P : SrcSem.SrcParams} {p : Prog}

/-- No extern step. -/
theorem none (h : P.hooks = SrcSem.SrcHooks.none) : HookOK P p := .inl h

/-- WeakCore's extern step, with no exit event in its event list at a
reachable configuration. -/
theorem wc (h : Scc.Sem.SrcOutProto.UsesWc P p)
    (hx : ∀ tr s, (SrcSem.source P p).Reach tr s → ∀ x, Ev.exit x ∉ P.hooks.trace s) : HookOK P p :=
  .inr ⟨h, hx⟩

/-- **The hook's event list ignores the threads.** -/
theorem trace_set (h : HookOK P p) (c : TermRun.Cfg) (ths : Array TermRun.TTh) :
    P.hooks.trace { c with ths := ths } = P.hooks.trace c := by
  rcases h with h | ⟨h, -⟩ <;> rw [h] <;> rfl

/-- **A machine step keeps the hook's event list.** -/
theorem trace_stepBy (h : HookOK P p) {i : Nat} {c c' : TermRun.Cfg}
    (hs : SrcSem.StepBy p P.k P.arch i c c') : P.hooks.trace c' = P.hooks.trace c := by
  rcases h with h | ⟨h, -⟩
  · rw [h]; rfl
  · rw [h]; simp only [SrcSem.wcHooks, SrcSem.traceOf, Scc.Sem.SrcOutProto.stepBy_trace hs]

/-- **No exit event in the hook's event list** at a reachable configuration. -/
theorem noExit (h : HookOK P p) {tr : List Ev} {s : TermRun.Cfg} (hr : (SrcSem.source P p).Reach tr s) :
    ∀ x, Ev.exit x ∉ P.hooks.trace s := by
  rcases h with h | ⟨-, hx⟩
  · rw [h]; intro x hx; cases hx
  · exact hx tr s hr

/-- `cutAtExit` keeps a list with no exit event. -/
theorem cutAtExit_of_noExit : ∀ {l : List Ev}, (∀ x, Ev.exit x ∉ l) → cutAtExit l = l
  | [], _ => rfl
  | e :: l, h => by
    cases e with
    | exit x => exact absurd (List.mem_cons_self ..) (h x)
    | _ => simp only [cutAtExit]; rw [cutAtExit_of_noExit fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `cutAtExit` of a list with no exit event, followed by `l'`: the list,
followed by `cutAtExit l'`. -/
theorem cutAtExit_append_of_noExit (l' : List Ev) : ∀ {l : List Ev}, (∀ x, Ev.exit x ∉ l) →
    cutAtExit (l ++ l') = l ++ cutAtExit l'
  | [], _ => rfl
  | e :: l, h => by
    cases e with
    | exit x => exact absurd (List.mem_cons_self ..) (h x)
    | _ =>
      simp only [List.cons_append, cutAtExit]
      rw [cutAtExit_append_of_noExit l' fun x hx => h x (List.mem_cons_of_mem _ hx)]

end HookOK

end Spike.Lib
