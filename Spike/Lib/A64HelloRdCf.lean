/-
**hello.w's `rodata` under the setup call's frame: the controls' run facts** (AArch64 consumers;
Option A). `rodata` is an ordinary source call of the setup wrapper (`SrcCalls.setupTerm_eq`): its states
run under the frame `frH env` the call pushes (`HelloPreTerm.frS`'s shape, returning into `r` then
`SrcCalls.setupCont`), and its `ret sl` pops that frame (`FrameStep.ret`). At no frame a local run cannot take that
pop (a `ret` takes no local step), which made the frameless statement vacuous after the fence (as hello1's
`Hello1.hand_sp0_empty`); here every fact is stated at `[frH env]`.

- `frH env`: the setup call's frame; `retJH fr Jr`: a control at `ret a` whose pop by `fr` lands in `Jr`
  (`Hello1.retJ`'s twin), `retJH_pop`.
- `helloTerms`, `GoodH`: the terms helloSrc's frame runs reach from the setup start up to the box's `new`
  (the wrapper, `rodata`'s body, `main`'s body to the `new`), the frames' bodies among them; `goodH_run`: kept
  by every frame run (a run stops at the `new`, `FrameNew.localStepS_not_new`).
- `runWf_goodH`: `RunWf` at a `GoodH` pair (no load or store; the only buffer is `rodata`'s, of lanes).
- `hcf_frH`: `rdPostW_WSH`/`rdPreW_WSH`'s control facts at `[frH env]` for a control whose term is among
  `helloTerms`, whatever it holds; `rd_terms`: `rodata`'s controls' terms are; `start_ctl`: the setup start
  control's facts at no frame (the start's `hc0`); `cont_ctl`: the wrapper's continuation's (`Jr`'s).
- `setup_call_run`: from the setup start, the call and `rodata`'s first two steps to `rdCN` under `frH env`.
- `rdRet_pop`, `setupCont_run`, `rdRet_box`: from `rdRet` under `frH env` the pop, the pair and the tail into
  `main`, and `main`'s steps to the box's `new` (`c0H`) at no frame.
- Non-vacuity (`rdRet_retJH`, the `example`s): the fence's landing `rdRet` under `frH env` is a `retJH` control of a
  nonempty `Jr` whose controls reach the box's allocation.
-/
import Spike.Lib.HelloMainPreSrc
import Spike.Lib.SrcCalls
import Spike.Lib.Hello1Runs
import Spike.Lib.FrameNew
import Spike.Lib.ZeroTy
import Spike.Lib.A64WakeWf

namespace Spike.Lib.HelloRdCf

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalStepS LocalRunS FrameStep FrameRun FenceRun)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloRodataSrc
open Spike.Lib.HelloMainPreSrc
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.Hello1RodataSrc (env0 τ8)

/-! ## The setup call's frame -/

/-- **The setup call's frame**: returning into `r`, then `SrcCalls.setupCont` in the wrapper's environment
`env`, at `rodata`'s return type. -/
def frH (env : Env) : Frame := ⟨"r", SrcCalls.setupCont, env, [], slTy⟩

/-- **A control at `ret a` whose pop by `fr` lands in `Jr`** (`Hello1.retJ`'s twin). -/
def retJH (fr : Frame) (Jr : Spike.Lib.A64.Flow.AS → Ctl → Prop) (σ : Spike.Lib.A64.Flow.AS) (c : Ctl) : Prop :=
  ∃ (a : At) (t : Ty) (ws : List Word), c.term = .ret a ∧ evalAt c.env a = some (t, ws) ∧
    Jr σ ⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩

/-- **The pop of a `retJH` control** is a frame step into `Jr`. -/
theorem retJH_pop {p : Prog} {fr : Frame} {Jr : Spike.Lib.A64.Flow.AS → Ctl → Prop} {σ : Spike.Lib.A64.Flow.AS}
    {c : Ctl} (h : retJH fr Jr σ c) (hσ : fr.σs = []) : ∃ c', FrameStep p (c, [fr]) (c', []) ∧ Jr σ c' := by
  obtain ⟨a, t, ws, ht, ha, hJ⟩ := h
  exact ⟨_, FrameStep.ret ht hσ ha, hJ⟩

/-! ## The terms of the runs up to the box -/

/-- **The terms helloSrc's runs reach from the setup start up to the box's `new`**: the wrapper and its
continuation, `rodata`'s body's suffixes, `main`'s body to the `new`. -/
def helloTerms : List Expr :=
  [Scc.Sem.SrcSem.setupTerm, SrcCalls.setupCont, .tail "main" [] (.var "a"),
    rdBody, eM, eB, eW0, eO0, eW1, eO1, eS, eN, eSm, eSl0, ePack, eRet,
    mainBodyH, zTerm, newTerm]

/-- **A pair the runs reach**: its term and every frame's body among `helloTerms`. -/
def GoodH (q : Ctl × List Frame) : Prop :=
  q.1.term ∈ helloTerms ∧ ∀ f ∈ q.2, f.body ∈ helloTerms

set_option hygiene false in
/-- `helloTerms`' definitions, for `simp`. -/
local macro "hT_simp" : tactic =>
  `(tactic| simp [Scc.Sem.SrcSem.setupTerm, SrcCalls.setupCont, rdBody, eM, eB, eW0, eO0, eW1, eO1, eS, eN, eSm,
    eSl0, ePack, eRet, mainBodyH, zTerm, newTerm, boxTermH, p0Term, pTerm, spawnTermH] at *)

/-- The body of a `let` other than the box's `new` among the terms is among them. -/
theorem let_mem {x : String} {op : Op} {e : Expr} (h : .let_ x op e ∈ helloTerms) (hn : ∀ a T, op ≠ .new a T) :
    e ∈ helloTerms := by
  simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (hT_simp; done)
    | (simp only [Scc.Sem.SrcSem.setupTerm, SrcCalls.setupCont, rdBody, eM, eB, eW0, eO0, eW1, eO1, eS, eN, eSm,
        eSl0, ePack, eRet, zTerm, newTerm, Expr.let_.injEq] at h
       obtain ⟨-, rfl, rfl⟩ := h
       first
       | exact (hn _ _ rfl).elim
       | simp [helloTerms, Scc.Sem.SrcSem.setupTerm, SrcCalls.setupCont, rdBody, eM, eB, eW0, eO0, eW1, eO1, eS, eN,
           eSm, eSl0, ePack, eRet, mainBodyH, zTerm, newTerm])

/-- A `split` among the terms is `main`'s, of body `zTerm`. -/
theorem split_mem {a : At} {x y : String} {e : Expr} (h : .split a x y e ∈ helloTerms) : e ∈ helloTerms := by
  simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (hT_simp; done)
    | (simp only [mainBodyH, Expr.split.injEq] at h
       obtain ⟨-, -, -, rfl⟩ := h
       simp [helloTerms])

/-- A tail call among the terms enters `main`. -/
theorem tail_mem {f : String} {is : List String} {a : At} {ts : List Ty} (h : .tail f is a ts ∈ helloTerms) :
    f = "main" := by
  simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> hT_simp
  exact h.1

/-- A call among the terms is the wrapper's call of `rodata`, of continuation `setupCont`. -/
theorem call_mem {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (h : .let_ x (.call f is a ts) e ∈ helloTerms) : f = "rodata" ∧ e = SrcCalls.setupCont := by
  simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (hT_simp; done)
    | (simp only [Scc.Sem.SrcSem.setupTerm, Expr.let_.injEq, Op.call.injEq] at h
       exact ⟨h.2.1.1, h.2.2⟩)

/-- `rodata` in `helloSrc`. -/
theorem rodata_find : helloSrc.find? (·.name == "rodata") = some (helloSrc[2]'(by decide)) := rfl

theorem rodata_body : (helloSrc[2]'(by decide)).body = rdBody := rfl

/-- **A local step keeps the terms.** -/
theorem term_localStepS {c c' : Ctl} (hs : LocalStepS helloSrc c c') (h : c.term ∈ helloTerms) :
    c'.term ∈ helloTerms := by
  cases hc : c.term with
  | let_ x op e =>
    rw [hc] at h
    cases op
    case call f is a ts => exact (Spike.Lib.LocalStepS.not_call hs hc).elim
    case new a => exact (Spike.Lib.FrameNew.localStepS_not_new hs hc).elim
    case callc f a =>
      exfalso
      simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> hT_simp
    all_goals
      rw [Spike.Lib.Hello1Runs.localStepS_let hs hc (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)]
      exact let_mem h fun _ _ h => by cases h
  | split a x y e => rw [Spike.Lib.Hello1Runs.localStepS_split hs hc]; exact split_mem (hc ▸ h)
  | tail f is a ts =>
    obtain ⟨d, hd, he⟩ := Spike.Lib.Hello1Runs.localStepS_tail hs hc
    have hf := tail_mem (hc ▸ h)
    subst hf
    rw [main_find] at hd
    cases hd
    rw [he]
    simp [helloTerms, mainD]
  | ret a => exact (Spike.Lib.Hello1Runs.localStepS_not_ret hs a hc).elim
  | _ =>
    exfalso
    rw [hc] at h
    simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> hT_simp

/-- **A frame step keeps `GoodH`.** -/
theorem goodH_step {q q' : Ctl × List Frame} (h : FrameStep helloSrc q q') (hg : GoodH q) : GoodH q' := by
  cases h with
  | loc hs => exact ⟨term_localStepS hs hg.1, hg.2⟩
  | @call c fs x f is a e d t ws ht hd ha =>
    obtain ⟨rfl, rfl⟩ := call_mem (ht ▸ hg.1)
    rw [rodata_find] at hd
    cases hd
    refine ⟨by rw [rodata_body]; simp [helloTerms], ?_⟩
    rintro f' hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · simp [helloTerms]
    · exact hg.2 f' hf'
  | @ret c fr fs a t ws ht hσ ha =>
    exact ⟨hg.2 fr List.mem_cons_self, fun f hf => hg.2 f (List.mem_cons_of_mem _ hf)⟩

/-- **A frame run keeps `GoodH`.** -/
theorem goodH_run {q q' : Ctl × List Frame} (h : FrameRun helloSrc q q') (hg : GoodH q) : GoodH q' := by
  induction h with
  | refl => exact hg
  | step hs _ ih => exact ih (goodH_step hs hg)

/-! ## The run obligations -/

/-- **`RunWf` at a `GoodH` pair**: no term among `helloTerms` loads or stores, and the only buffer allocation
(`rodata`'s) is of lanes, whose zero words are zero. -/
theorem runWf_goodH {c : Ctl} {fs : List Frame} (hg : GoodH (c, fs)) : RunWf helloSrc c fs := by
  refine ⟨fun c' fs' hr x a e ty w ht _ => ?_, fun c' fs' hr x a τ e ht => ?_⟩
  · exfalso
    have h1 := (goodH_run hr hg).1
    simp only at h1
    rcases ht with ht | ⟨b, ht⟩ <;> rw [ht] at h1 <;>
    · simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> hT_simp
  · have h1 := (goodH_run hr hg).1
    simp only at h1
    rw [ht] at h1
    simp only [helloTerms, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      first
      | (hT_simp; done)
      | (simp only [eB, Expr.let_.injEq, Op.newBuf.injEq] at h
         obtain ⟨-, ⟨-, rfl⟩, -⟩ := h
         exact Spike.Lib.zeroOkTy_lanes false .w8)

/-- **The control facts under the setup call's frame**: a control whose term is among `helloTerms` (holding
anything) has its runs well formed at `[frH env]`; the no-`ret` clause is vacuous there. -/
theorem hcf_frH {c : Ctl} {env : Env} (hc : c.term ∈ helloTerms) :
    ([frH env] = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [frH env] :=
  ⟨fun h => (List.cons_ne_nil _ _ h).elim, runWf_goodH ⟨hc, fun f hf => by
    rw [List.mem_singleton.mp hf]; simp [frH, helloTerms]⟩⟩

/-- **`rodata`'s controls' terms** are among `helloTerms`. -/
theorem rd_terms (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    rdC0.term ∈ helloTerms ∧ rdCN.term ∈ helloTerms ∧ (rdCA l ini).term ∈ helloTerms ∧
      (rdC1 l ini).term ∈ helloTerms ∧ (rdC2 l ini wo0).term ∈ helloTerms ∧ (rdC3 l ini wo0).term ∈ helloTerms ∧
      (rdC4 l ini wo0 wo1).term ∈ helloTerms ∧ (rdC5 l ini wo0 wo1).term ∈ helloTerms ∧
      (rdRet l ini wo0 wo1).term ∈ helloTerms := by
  simp [helloTerms, rdC0, rdCN, rdCA, rdC1, rdC2, rdC3, rdC4, rdC5, rdRet]

/-- **The setup start's control facts** (the start's `hc0`): not a `ret`, its runs well formed at no frame. -/
theorem start_ctl (env : Env) :
    (∀ a, (⟨Scc.Sem.SrcSem.setupTerm, env, none⟩ : Ctl).term ≠ .ret a) ∧
      RunWf helloSrc ⟨Scc.Sem.SrcSem.setupTerm, env, none⟩ [] :=
  ⟨fun _ h => by simp [Scc.Sem.SrcSem.setupTerm] at h, runWf_goodH ⟨by simp [helloTerms], fun _ h => nomatch h⟩⟩

/-- **The wrapper's continuation's control facts** (`rodata`'s return invariant `Jr`): not a `ret`, its runs
well formed at no frame. -/
theorem cont_ctl (env : Env) (h : Option (Nat × Word)) :
    (∀ a, (⟨SrcCalls.setupCont, env, h⟩ : Ctl).term ≠ .ret a) ∧ RunWf helloSrc ⟨SrcCalls.setupCont, env, h⟩ [] :=
  ⟨fun _ h => by simp [SrcCalls.setupCont] at h, runWf_goodH ⟨by simp [helloTerms], fun _ h => nomatch h⟩⟩

/-! ## The call, the return, and on to the box -/

/-- **From the setup start to `rodata`'s buffer allocation**: the call (`u` the unit in `env`) pushes `frH env`,
then `rodata`'s first two local steps (`rdC0_run`). -/
theorem setup_call_run {env : Env} (hu : evalAt env (.var "u") = some (.unit, [])) :
    FrameRun helloSrc (⟨Scc.Sem.SrcSem.setupTerm, env, none⟩, []) (rdCN, [frH env]) :=
  .step (FrameStep.call (x := "r") (f := "rodata") (a := .var "u") (e := SrcCalls.setupCont) rfl rodata_find hu)
    (FrameRun.ofLocal rdC0_run _)

/-- The slice's words `rodata` returns, at the buffer's label `l`. -/
def slW (l : WeakMem.AllocLabel) : List Word := [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]

/-- **`rodata`'s return pops `frH env`** into the wrapper's continuation with `r` bound to the slice. -/
theorem rdRet_pop (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) (env : Env) :
    FrameStep helloSrc (rdRet l ini wo0 wo1, [frH env]) (⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩, []) :=
  FrameStep.ret (rdRet_ret l ini wo0 wo1).1 rfl (rdRet_ret l ini wo0 wo1).2.2

/-- **The wrapper's continuation runs into `main`**: the pair of `r` with `me` (one word `mw` in `env`), the
tail call, at `main`'s entry `mainC`. -/
theorem setupCont_run {l : WeakMem.AllocLabel} {env : Env} {tm : Ty} {mw : Word}
    (hme : evalAt env (.var "me") = some (tm, [mw])) :
    LocalRunS helloSrc ⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩
      (mainC (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw) := by
  have hme' : evalAt (("r", slTy, slW l) :: env) (.var "me") = some (tm, [mw]) := by
    simpa [evalAt, lookupE] using hme
  exact .step (Spike.Lib.localStepS_pair rfl rfl hme') (.single (Spike.Lib.localStepS_tail rfl main_find rfl))

/-- **From `rodata`'s return to the box's allocation**: the pop, the continuation into `main`, `main`'s split and
zero (`c0H_run`), at no frame. -/
theorem rdRet_box {l : WeakMem.AllocLabel} {ini : Nat} {wo0 wo1 : Word} {env : Env} {tm : Ty} {mw : Word}
    (hme : evalAt env (.var "me") = some (tm, [mw])) :
    FrameRun helloSrc (rdRet l ini wo0 wo1, [frH env])
      (c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw, []) :=
  .step (rdRet_pop l ini wo0 wo1 env) (FrameRun.ofLocalS ((setupCont_run hme).trans (c0H_run _ _ _ _)) [])

/-! ## Non-vacuity -/

/-- **The canonical return invariant**: the wrapper's continuation on `rodata`'s slice at some label. -/
def JrH (env : Env) (_ : Spike.Lib.A64.Flow.AS) (c : Ctl) : Prop :=
  ∃ l, c = ⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩

/-- **The fence's landing `rdRet` under `frH env` is a `retJH` control** of `JrH env`. -/
theorem rdRet_retJH (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) (env : Env) (σ : Spike.Lib.A64.Flow.AS) :
    retJH (frH env) (JrH env) σ (rdRet l ini wo0 wo1) :=
  ⟨_, _, _, (rdRet_ret l ini wo0 wo1).1, (rdRet_ret l ini wo0 wo1).2.2, l, rfl⟩

/-- **`JrH`'s controls reach the box's allocation**, at no frame. -/
theorem jrH_box {env : Env} {tm : Ty} {mw : Word} (hme : evalAt env (.var "me") = some (tm, [mw]))
    {σ : Spike.Lib.A64.Flow.AS} {c : Ctl} (h : JrH env σ c) :
    ∃ l, LocalRunS helloSrc c (c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw) := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨l, (setupCont_run hme).trans (c0H_run _ _ _ _)⟩

/-- The non-vacuity, concretely: from the second exchange's landing `rdC4` under the setup frame the fence's run
reaches `rdRet`, a `retJH` control whose pop lands in `JrH` (nonempty), from which `main` reaches the box. -/
example (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) (σ : Spike.Lib.A64.Flow.AS) :
    FenceRun helloSrc True .st (rdC4 l ini wo0 wo1) (rdRet l ini wo0 wo1) ∧
      retJH (frH [("me", .tid, [cst (.num 7)]), ("u", .unit, [])])
        (JrH [("me", .tid, [cst (.num 7)]), ("u", .unit, [])]) σ (rdRet l ini wo0 wo1) ∧
      FrameRun helloSrc (rdRet l ini wo0 wo1, [frH [("me", .tid, [cst (.num 7)]), ("u", .unit, [])]])
        (c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) (cst (.num 7)), []) :=
  ⟨rdC4_fence trivial l ini wo0 wo1, rdRet_retJH l ini wo0 wo1 _ σ, rdRet_box rfl⟩

/-- The setup start reaches `rodata`'s allocation under the setup frame. -/
example : FrameRun helloSrc (⟨Scc.Sem.SrcSem.setupTerm, [("me", .tid, [cst (.num 7)]), ("u", .unit, [])], none⟩, [])
    (rdCN, [frH [("me", .tid, [cst (.num 7)]), ("u", .unit, [])]]) :=
  setup_call_run rfl

end Spike.Lib.HelloRdCf

/-- info: 'Spike.Lib.HelloRdCf.runWf_goodH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRdCf.runWf_goodH

/-- info: 'Spike.Lib.HelloRdCf.hcf_frH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRdCf.hcf_frH

/-- info: 'Spike.Lib.HelloRdCf.start_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRdCf.start_ctl

/-- info: 'Spike.Lib.HelloRdCf.setup_call_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRdCf.setup_call_run

/-- info: 'Spike.Lib.HelloRdCf.rdRet_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRdCf.rdRet_box
