import Spike.Lib.Src.SliceL
import Spike.Lib.Seg

/-!
**The output extern's element loads read written cells** (ISA-neutral).
From the extern's entry on a slice (a locative of label `l` and a count `m`
whose first `m` cells have messages), every run of the extern's frame steps
(`TStepE`: a thread step but a return or a call, or an extern step) reaches
the loop's element load (`PrintLd`) only at a cell of `l` below `m`
(`ldOK_print`): the loop keeps "the buffer's first `i + 1 + d` cells have
messages" at its top (`ldOK_loop`, by induction on the run's length).

- `printLoadE`, `PrintLd`: the load and its trigger;
- `TStepE`, `TRunE`, `LdOK`: the frame steps, their runs, the property;
  `LdOK.step`, `.mono`, `LocalStep.tstepE`, `localRun_trunE`;
- `tstepE_let`, `_split`, `_ifeq`, `_tail`, `_ret`, `_unpack`, `_call`: the
  steps of each form.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm TermRun

/-! ## The load -/

/-- **The print loop's element load**: `printLBody` from its `loadAt`. -/
def printLoadE : Expr := .let_ "wd" (.loadAt (.var "b") (.var "iv"))
  (.let_ "x" (.lane (.var "wd") (.var "j")) (.let_ "r" (.ext .emit (.var "x")) Scc.Frontend.printNext))

/-- **A load of word `j` of label `l`** by the print loop: at `printLoadE`,
`b` bound to the buffer's locative and `iv` to `j`. -/
def PrintLd (c : Ctl) (l : WeakMem.AllocLabel) (j : Nat) : Prop :=
  c.term = printLoadE ∧
  (∃ t w, lookupE c.env "b" = some (t, [w]) ∧ w.val = .loc ⟨l, 0⟩ 0) ∧
  (∃ t w, lookupE c.env "iv" = some (t, [w]) ∧ w.val = .num j)

/-! ## The frame steps -/

/-- Neither a return nor a call. -/
def NoRC (t : Expr) : Prop := (∀ a, t ≠ .ret a) ∧ ∀ x f is a ts e, t ≠ .let_ x (.call f is a ts) e

/-- **A step of a frame** (term and environment): a thread step that neither
returns nor calls, at any surroundings, or an extern step binding any
result. -/
def TStepE (p : Prog) (c c1 : Expr × Env) : Prop :=
  (∃ (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh) (r : WeakMem.Memory × List WeakMem.Ts × TTh),
      g.p = p ∧ th.term = c.1 ∧ th.env = c.2 ∧ NoRC c.1 ∧ r ∈ tstep g mem pairs th ∧ r.2.2.term = c1.1 ∧
      r.2.2.env = c1.2) ∨
    ∃ x n a e t ws, c.1 = .let_ x (.ext n a) e ∧ c1 = (e, (x, t, ws) :: c.2)

/-- `n` frame steps. -/
inductive TRunE (p : Prog) : Nat → Expr × Env → Expr × Env → Prop
  | refl (c : Expr × Env) : TRunE p 0 c c
  | step {n : Nat} {c c1 c' : Expr × Env} : TStepE p c c1 → TRunE p n c1 c' → TRunE p (n + 1) c c'

/-- **Every load the frame's runs reach reads a cell with a message.** -/
def LdOK (p : Prog) (mem : WeakMem.Memory) (c : Expr × Env) : Prop :=
  ∀ n c' l j, TRunE p n c c' → PrintLd ⟨c'.1, c'.2, none⟩ l j → HasCell mem ⟨l, j⟩

variable {p : Prog}

theorem LdOK.step {mem : WeakMem.Memory} {c c1 : Expr × Env} (h : LdOK p mem c) (hs : TStepE p c c1) :
    LdOK p mem c1 :=
  fun n c' l j hr hl => h (n + 1) c' l j (.step hs hr) hl

theorem LdOK.mono {mem mem' : WeakMem.Memory} {c : Expr × Env} (h : LdOK p mem c) (hm : TermCert.MemExt mem mem') :
    LdOK p mem' c :=
  fun n c' l j hr hl => let ⟨k, m, hk, hl'⟩ := h n c' l j hr hl; ⟨k, m, hm k m hk, hl'⟩

/-- **A local step is a frame step.** -/
theorem LocalStep.tstepE {c c1 : Ctl} (h : LocalStep p c c1) : TStepE p (c.term, c.env) (c1.term, c1.env) := by
  let g : G := ⟨p, Promises.Knobs.all, .arm, 0, 0, 0, true, fun _ => False, fun _ => True, fun _ => none⟩
  let th : TTh := { term := c.term, env := c.env }
  have hs := h.2 g #[] [] th rfl rfl rfl rfl rfl
  refine Or.inl ⟨g, #[], [], th, _, rfl, rfl, rfl, ⟨fun a ha => ?_, fun x f is a ts e ha => ?_⟩,
    by rw [hs]; exact List.mem_singleton_self _, rfl, rfl⟩
  · have ha' : c.term = _ := ha
    simp [th, tstep, ha'] at hs
  · have ha' : c.term = _ := ha
    simp [th, tstep, ha', ol, callFrame, enter] at hs
    cases hd : List.find? (fun x => x.name == f) g.p <;> simp [hd] at hs
    cases hev : evalAt c.env a <;> simp [hev] at hs

/-! ## The steps of each form -/

theorem tstepE_ret {a : At} {env : Env} {c1 : Expr × Env} : ¬ TStepE p (.ret a, env) c1 := by
  rintro (⟨_, _, _, _, _, -, -, -, ⟨h, -⟩, -⟩ | ⟨_, _, _, _, _, _, h, -⟩)
  · exact h a rfl
  · cases h

/-- **A `let` but a call**: its body, the result bound (an extern's, or an
operation's). -/
theorem tstepE_let {x : String} {op : Op} {e : Expr} {env : Env} {c1 : Expr × Env}
    (h : TStepE p (.let_ x op e, env) c1) (hc : ∀ f is a ts, op ≠ .call f is a ts) (hcc : ∀ f a, op ≠ .callc f a) :
    ∃ t ws, c1 = (e, (x, t, ws) :: env) ∧
      ((∃ n a, op = .ext n a) ∨ ∃ g σs st s', (s', t, ws) ∈ evalOp g env σs st op) := by
  rcases h with ⟨g, mem, pairs, th, r, -, ht, he, -, hr, h1, h2⟩ | ⟨x', n, a, e', t, ws, hx, rfl⟩
  · by_cases hn : ∃ a T, op = .new a T
    · obtain ⟨a, T, rfl⟩ := hn
      obtain ⟨s', t, ws, hev, tys, rfl⟩ := TermRun.tstep_new_mem (by simpa using ht) hr
      simp only [withS] at h1 h2
      subst he
      exact ⟨t, ws, Prod.ext h1.symm h2.symm, Or.inr ⟨g, th.σs, _, s', hev⟩⟩
    have hts : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map fun (s', t, ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
      cases op <;> first | exact absurd rfl (hc _ _ _ _) | exact absurd rfl (hcc _ _) | exact (hn ⟨_, _, rfl⟩).elim | simp [tstep, ht]
    rw [hts] at hr
    obtain ⟨⟨s', t, ws⟩, hev, rfl⟩ := List.mem_map.1 hr
    simp only [withS] at h1 h2
    subst he
    exact ⟨t, ws, Prod.ext h1.symm h2.symm, Or.inr ⟨g, th.σs, _, s', hev⟩⟩
  · simp only [Expr.let_.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨t, ws, rfl, Or.inl ⟨n, a, rfl⟩⟩

/-- **A split**: the pair's parts bound. -/
theorem tstepE_split {a : At} {x y : String} {e : Expr} {env : Env} {c1 : Expr × Env}
    (h : TStepE p (.split a x y e, env) c1) :
    ∃ u w ws us, evalAt env a = some (.prod u w, ws) ∧ accs u = some us ∧
      c1 = (e, (y, w, ws.drop (nWords us)) :: (x, u, ws.take (nWords us)) :: env) := by
  rcases h with ⟨g, mem, pairs, th, r, -, ht, he, -, hr, h1, h2⟩ | ⟨_, _, _, _, _, _, hx, -⟩
  · subst he
    simp only [tstep, ht] at hr
    split at hr <;> try (simp at hr; done)
    split at hr <;> try (simp at hr; done)
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, _, _, _, ‹_›, ‹_›, Prod.ext h1.symm h2.symm⟩
  · cases hx

/-- **An `if`**: a branch, the same environment; on two numbers, the
branch of their equality. -/
theorem tstepE_ifeq {a b : At} {yes no : Expr} {env : Env} {c1 : Expr × Env}
    (h : TStepE p (.ifeq a b yes no, env) c1) :
    c1.2 = env ∧ (c1.1 = yes ∨ c1.1 = no) ∧ ∀ ta tb wa wb n m, evalAt env a = some (ta, [wa]) →
      evalAt env b = some (tb, [wb]) → wa.val = .num n → wb.val = .num m → c1.1 = if n = m then yes else no := by
  rcases h with ⟨g, mem, pairs, th, r, -, ht, he, -, hr, h1, h2⟩ | ⟨_, _, _, _, _, _, hx, -⟩
  · subst he
    simp only [tstep, ht] at hr
    split at hr <;> try (simp at hr; done)
    rename_i ta wa tb wb hea heb
    split at hr <;> try (simp at hr; done)
    all_goals
      simp only [List.mem_singleton] at hr
      subst hr
      rw [← h1, ← h2]
      refine ⟨rfl, by split <;> simp, ?_⟩
      intro ta' tb' wa' wb' n' m' ha hb hna hnb
      rw [hea] at ha; rw [heb] at hb
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at ha hb
      obtain ⟨-, rfl⟩ := ha; obtain ⟨-, rfl⟩ := hb
      simp_all
  · cases hx

/-- **A tail call without type arguments**: the callee's body, its
parameter bound. -/
theorem tstepE_tail {f : String} {is : List String} {a : At} {env : Env} {c1 : Expr × Env}
    (h : TStepE p (.tail f is a [], env) c1) :
    ∃ d t ws, p.find? (·.name == f) = some d ∧ evalAt env a = some (t, ws) ∧
      c1 = (d.body, [(d.arg, close [] d.argTy, ws)]) := by
  rcases h with ⟨g, mem, pairs, th, r, hg, ht, he, -, hr, h1, h2⟩ | ⟨_, _, _, _, _, _, hx, -⟩
  · subst he hg
    simp only [tstep, ht, ol, enter, Option.bind_eq_bind, Option.pure_def, Option.toList] at hr
    cases hd : g.p.find? (·.name == f) <;> cases hev : evalAt th.env a <;> simp [hd, hev] at hr
    subst hr
    exact ⟨_, _, _, rfl, rfl, Prod.ext h1.symm h2.symm⟩
  · cases hx

/-- **An index unpack**: its body. -/
theorem tstepE_unpack {a : At} {i x : String} {e : Expr} {env : Env} {c1 : Expr × Env}
    (h : TStepE p (.unpack a i x e, env) c1) : c1.1 = e := by
  rcases h with ⟨g, mem, pairs, th, r, -, ht, he, -, hr, h1, -⟩ | ⟨_, _, _, _, _, _, hx, -⟩
  · simp only [tstep, ht] at hr
    split at hr <;> try (simp at hr; done)
    simp only [List.mem_singleton] at hr
    subst hr
    exact h1.symm
  · cases hx

/-- A call is no frame step. -/
theorem tstepE_call {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr} {env : Env}
    {c1 : Expr × Env} : ¬ TStepE p (.let_ x (.call f is a ts) e, env) c1 := by
  rintro (⟨_, _, _, _, _, -, -, -, ⟨-, h⟩, -⟩ | ⟨_, _, _, _, _, _, h, -⟩)
  · exact h x f is a ts e rfl
  · cases h

/-- **A local run is a run of frame steps.** -/
theorem localRun_trunE {c c' : Ctl} (h : LocalRun p c c') : ∃ n, TRunE p n (c.term, c.env) (c'.term, c'.env) := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | step hs _ ih =>
    obtain ⟨n, hr⟩ := ih
    exact ⟨n + 1, .step (LocalStep.tstepE hs) hr⟩

/-! ## The loop and the extern -/

set_option hygiene false in
/-- A run at a term that is no load: its first step. -/
local macro "run_step" : tactic => `(tactic| (
  cases hr
  · exact absurd hld.1 (by simp [printLoadE])
  rename_i c1 hs hr))

set_option hygiene false in
/-- A split's step, the pair's type and words known. -/
local macro "run_split" : tactic => `(tactic| (
  run_step
  obtain ⟨_, _, _, _, hev, hus, rfl⟩ := tstepE_split hs
  simp only [evalAt, lookupE_cons, ite_true, ite_false, reduceCtorEq, String.reduceEq, Option.some.injEq,
    Prod.mk.injEq, Ty.prod.injEq] at hev
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hev
  simp [accs, Scc.Frontend.printLBufTy] at hus
  subst hus
  simp only [nWords, Acc.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero] at hr))

set_option hygiene false in
/-- A `let`'s step, the result's words known. -/
local macro "run_let" : tactic => `(tactic| (
  run_step
  obtain ⟨_, _, rfl, ⟨_, _, hx⟩ | ⟨_, _, _, _, hev⟩⟩ := tstepE_let hs (by intros; simp) (by intros; simp)
  · cases hx
  simp [evalOp, ol, evalAt, lookupE_cons] at hev
  obtain ⟨-, rfl, rfl⟩ := hev))

set_option hygiene false in
/-- A `let`'s step, the result's words unknown. -/
local macro "run_any" : tactic => `(tactic| (
  run_step
  obtain ⟨_, _, rfl, -⟩ := tstepE_let hs (by intros; simp) (by intros; simp)))

set_option hygiene false in
/-- An `if`'s step: either branch. -/
local macro "run_if" : tactic => `(tactic| (
  run_step
  obtain ⟨h2, h1, -⟩ := tstepE_ifeq hs
  obtain ⟨t1, e1⟩ := c1
  simp only at h1 h2
  subst h2
  rcases h1 with rfl | rfl))

set_option hygiene false in
/-- A return: no step. -/
local macro "run_ret" : tactic => `(tactic| (
  run_step
  exact absurd hs tstepE_ret))

/-- **The loop keeps its buffer's cells**: from the loop's top with the
buffer `l`, word `i` and `d` words left, the first `i + 1 + d` cells of `l`
having messages, every run reaches the load only at a cell of `l` below
`i + 1 + d`. -/
theorem ldOK_loop {mem : WeakMem.Memory} (hf : p.find? (·.name == "printL") = some Scc.Frontend.printLoopD) :
    ∀ n (i d : Nat) (l : WeakMem.AllocLabel) (w0 wi wd : Word) (rest : List Word), w0.val = .loc ⟨l, 0⟩ 0 →
      wi.val = .num i → wd.val = .num d → (∀ k < i + 1 + d, HasCell mem ⟨l, k⟩) → ∀ c' l' j,
      TRunE p n (Scc.Frontend.printLBody, [("a", Scc.Frontend.printLTy, w0 :: wi :: wd :: rest)]) c' →
        PrintLd ⟨c'.1, c'.2, none⟩ l' j → HasCell mem ⟨l', j⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro i d l w0 wi wd rest h0 hi hd hc c' l' j hr hld
  simp only [Scc.Frontend.printLBody] at hr
  run_split
  run_split
  run_split
  run_split
  run_split
  run_if
  · run_ret
  run_if
  · -- `j = 8`: the last word, or the next one (`printAdv`)
    run_step
    obtain ⟨h2, -, h3⟩ := tstepE_ifeq hs
    obtain ⟨t1, e1⟩ := c1
    have h1 := h3 _ _ wd (cst (.num 0)) d 0 (by simp [evalAt, lookupE_cons] <;> rfl) rfl hd rfl
    simp only at h1 h2
    subst h1 h2
    by_cases hd0 : d = 0
    · simp only [hd0, ite_true] at hr
      run_ret
    simp only [hd0, ite_false, Scc.Frontend.printAdv] at hr
    run_let
    run_let
    run_let
    run_let
    run_let
    run_let
    run_any
    run_any
    run_let
    run_step
    obtain ⟨d', t, ws, hfd, hev, rfl⟩ := tstepE_tail hs
    rw [hf] at hfd; cases hfd
    simp [evalAt, lookupE_cons] at hev
    obtain ⟨-, rfl⟩ := hev
    rw [show close [] Scc.Frontend.printLoopD.argTy = Scc.Frontend.printLTy from TermStep.substTs_nil' _ 0 0] at hr
    exact ih _ (by omega) (i + 1) (d - 1) l w0 _ _ _ h0 (by simp [addW, hi, cst, Promises.TVal.mk0])
      (by simp [subW, hd, cst, Promises.TVal.mk0]) (fun k hk => hc k (by omega)) c' l' j hr hld
  · -- the load, then its byte's emission and the next byte (`printNext`)
    cases hr
    · obtain ⟨-, ⟨t, w, hb, hw⟩, ⟨t', w', hiv, hw'⟩⟩ := hld
      simp [lookupE_cons] at hb hiv
      obtain ⟨-, rfl⟩ := hb
      obtain ⟨-, rfl⟩ := hiv
      rw [h0] at hw; rw [hi] at hw'
      simp only [WeakMem.Val.loc.injEq, WeakMem.Val.num.injEq, WeakMem.Address.mk.injEq] at hw hw'
      obtain ⟨⟨rfl, -⟩, -⟩ := hw
      subst hw'
      exact hc i (by omega)
    rename_i c1 hs hr
    obtain ⟨_, _, rfl, -⟩ := tstepE_let hs (by intros; simp) (by intros; simp)
    run_any
    run_any
    simp only [Scc.Frontend.printNext] at hr
    run_any
    run_any
    run_any
    run_any
    run_let
    run_let
    run_let
    run_step
    obtain ⟨d', t, ws, hfd, hev, rfl⟩ := tstepE_tail hs
    rw [hf] at hfd; cases hfd
    simp [evalAt, lookupE_cons] at hev
    obtain ⟨-, rfl⟩ := hev
    rw [show close [] Scc.Frontend.printLoopD.argTy = Scc.Frontend.printLTy from TermStep.substTs_nil' _ 0 0] at hr
    exact ih _ (by omega) i d l w0 wi wd _ h0 hi hd hc c' l' j hr hld

/-- **The extern's loads read written cells**: entered on a slice (a
locative of label `l` and a count `m` whose first `m` cells have messages),
its runs reach the loop's top at word 0 with `m - 1` words left
(`ldOK_loop`), or return on `m = 0`. -/
theorem ldOK_print {mem : WeakMem.Memory} (hf : p.find? (·.name == "printL") = some Scc.Frontend.printLoopD)
    {l : WeakMem.AllocLabel} {m : Nat} {w0 w1 : Word} {rest : List Word} (h0 : w0.val = .loc ⟨l, 0⟩ 0)
    (h1 : w1.val = .num m) (hc : ∀ k < m, HasCell mem ⟨l, k⟩) :
    LdOK p mem (Scc.Frontend.printBody, [("a", close [] Scc.Frontend.ownSliceTy, w0 :: w1 :: rest)]) := by
  intro n c' l' j hr hld
  rw [show close [] Scc.Frontend.ownSliceTy = Scc.Frontend.ownSliceTy from TermStep.substTs_nil' _ 0 0] at hr
  simp only [Scc.Frontend.printBody] at hr
  run_split
  run_split
  run_step
  obtain ⟨h2, -, h3⟩ := tstepE_ifeq hs
  obtain ⟨t1, e1⟩ := c1
  have h4 := h3 _ _ w1 (cst (.num 0)) m 0 (by simp [evalAt, lookupE_cons] <;> rfl) rfl h1 rfl
  simp only at h4 h2
  subst h4 h2
  by_cases hm0 : m = 0
  · simp only [hm0, ite_true] at hr
    run_ret
  simp only [hm0, ite_false] at hr
  run_let
  run_let
  run_let
  run_let
  run_let
  run_let
  run_let
  run_let
  run_let
  run_let
  run_step
  obtain ⟨d', t, ws, hfd, hev, rfl⟩ := tstepE_tail hs
  rw [hf] at hfd; cases hfd
  simp [evalAt, lookupE_cons] at hev
  obtain ⟨-, rfl⟩ := hev
  rw [show close [] Scc.Frontend.printLoopD.argTy = Scc.Frontend.printLTy from TermStep.substTs_nil' _ 0 0] at hr
  exact ldOK_loop hf _ 0 (m - 1) l w0 _ _ _ h0 (by simp [cst, Promises.TVal.mk0])
    (by simp [subW, h1, cst, Promises.TVal.mk0]) (fun k hk => hc k (by omega)) c' l' j hr hld

end Spike.Lib.LowerNode
