/-
**Programs without `publish`** discharge WeakCore's two certificate-window
obligations (`TermCertScope.CertWinCNX`, `CertWinPNX`), so that M1 takes its
typing facts (`Scc/Sem/Typing.lean` `SrcTyped`) from WeakCore's token
soundness theorems (`SpawnArmZ.machine_tokens_main_spawn`,
`TermMain.machine_tokens_mainF`) with no named run fact left.

The windows ask, along every certified solo run, for `NoHoldPubN`: at every
typing of the thread, `PubWinTN`, a premise about a thread whose term is
`let x = publish a in e`. A thread none of whose code contains `publish`
never is at one, so the premise is vacuous. The proof is TermScope's
`RunScope` argument with `allOK` replaced by `pubFree`:

- **The check.** `pubFree`: no `let _ = publish _` in any subterm (TermScope's
  `allOK` shape); `ProgPubFree p`: every code block's body (decidable).
- **The invariant.** `ThPF`: a thread's term and every stack frame's body are
  `pubFree`; `RunPF`: every thread. `tstep_pf`: a thread step keeps `ThPF`
  (TermScope's `tstep_drf` without the environment and type-argument parts;
  `call`, `callc`, `tail` enter a code block's body, from `p`).
- **Along runs.** `pf_thread`, `pf_prom`, `solo_pf` (solo runs);
  `runPF_step`, `runPF_spawnStep`, `RunPFR`, `runPFR_of`, `runPFR_spawn`,
  `runPFR_bot` (runs with an extra relation `Sp`, the `Spawn` arm included);
  `runPF_init`: the start condition for the `spawn` shape.
- **The windows.** `noHoldPubN_of`; `certWinCNX_of_noPublish`,
  `certWinPNX_of_noPublish` (and `certWinCN_of_noPublish`,
  `certWinPN_of_noPublish`, over runs without spawns).
- **Typing.** `obligationsFX_of_noPublish`, `srcTyped_spawn_of_noPublish`
  (from `machine_tokens_main_spawn`); `obligationsF_of_noPublish`,
  `srcTyped_mainF_of_noPublish` (from `machine_tokens_mainF`).
-/
import Scc.Sem.Typing
import WeakCore.SpawnArmZ

namespace Scc.Sem.PubFree

open CoreLang CoreTerm CoreTyping TermRun TermSound TermMain TermCertScope TermSpawnStep TermTyped
open WeakMem (Arch Address Ts)

/-! ## The check -/

/-- Is the operation `publish`? -/
def isPublish : Op → Bool
  | .publish _ => true
  | _ => false

/-- **No `publish` in the term** (any subterm; TermScope's `allOK` shape). -/
def pubFree : Expr → Bool
  | .let_ _ op e => !isPublish op && pubFree e
  | .split _ _ _ e => pubFree e
  | .unpack _ _ _ e => pubFree e
  | .unpackT _ _ _ e => pubFree e
  | .region _ _ _ _ e => pubFree e
  | .openPub _ _ _ _ e => pubFree e
  | .case _ _ e₁ _ e₂ => pubFree e₁ && pubFree e₂
  | .ifnull _ e₁ _ e₂ => pubFree e₁ && pubFree e₂
  | .parity _ _ e₁ e₂ => pubFree e₁ && pubFree e₂
  | .ifeq _ _ e₁ e₂ => pubFree e₁ && pubFree e₂
  | .cas _ _ _ _ _ _ ok fail => pubFree ok && pubFree fail
  | .casp _ _ _ _ _ _ _ _ ok fail => pubFree ok && pubFree fail
  | .ret _ => true
  | .tail _ _ _ _ => true

/-- **The program has no `publish`**: no code block's body has one. -/
def ProgPubFree (p : Prog) : Prop := p.all (fun d => pubFree d.body) = true

instance (p : Prog) : Decidable (ProgPubFree p) := inferInstanceAs (Decidable (_ = true))

theorem ProgPubFree.decl {p : Prog} (hp : ProgPubFree p) {d : Decl} (hd : d ∈ p) : pubFree d.body = true :=
  List.all_eq_true.1 hp d hd

/-! ## The invariant -/

/-- **A thread without `publish`**: its term and every suspended frame's body. -/
structure ThPF (th : TTh) : Prop where
  term : pubFree th.term = true
  stk : ∀ f ∈ th.stack, pubFree f.body = true

/-- **Every thread without `publish`.** -/
def RunPF (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThPF th

/-- Entering a code block of a publish-free program. -/
theorem enter_pf {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At} (hp : ProgPubFree g.p)
    (h : enter g th f ts a = some th') : pubFree th'.term = true ∧ th'.stack = th.stack := by
  unfold enter at h
  cases hd : g.p.find? (·.name == f) with
  | none => simp [hd] at h
  | some d =>
  cases hev : evalAt th.env a with
  | none => simp [hd, hev] at h
  | some p =>
  simp [hd, hev] at h
  subst h
  exact ⟨hp.decl (List.mem_of_find?_eq_some hd), rfl⟩

/-- The frame a call pushes has the call's continuation as its body. -/
theorem callFrame_body {g : G} {th : TTh} {f : String} {ts : List Ty} {x : String} {e : Expr} {fr : Frame}
    (h : callFrame g th f ts x e = some fr) : fr.body = e := by
  unfold callFrame at h
  cases hd : g.p.find? (·.name == f) with
  | none => simp [hd] at h
  | some d => simp [hd] at h; subst h; rfl

/-- **`tstep` keeps `ThPF`** for a publish-free program. -/
theorem tstep_pf {g : G} {mem : WeakMem.Memory} {pairs : List Ts} {th : TTh}
    {r : WeakMem.Memory × List Ts × TTh} (hp : ProgPubFree g.p) (h : ThPF th)
    (hr : r ∈ tstep g mem pairs th) : ThPF r.2.2 := by
  obtain ⟨hok, hstk⟩ := h
  unfold tstep at hr
  split at hr
  · -- call
    rename_i _ x f is a ts e heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    cases hcf : callFrame g th f ts x e with
    | none => simp [hcf, ol] at hr
    | some fr =>
      cases hen : enter g { th with stack := fr :: th.stack } f ts a with
      | none => simp [hcf, hen, ol] at hr
      | some th' =>
        simp only [hcf, hen, ol, Option.bind_some, Option.map_some, Option.toList_some,
          List.mem_singleton] at hr
        subst hr
        obtain ⟨h1, h2⟩ := enter_pf hp hen
        refine ⟨h1, ?_⟩
        rw [h2]
        intro f' hf'
        rcases List.mem_cons.1 hf' with rfl | hf'
        · rw [callFrame_body hcf]; exact hok.2
        · exact hstk f' hf'
  · -- callc
    rename_i _ x f a e heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · rename_i tf w _
      split at hr
      · split at hr
        · rename_i d hd
          cases hcf : callFrame g th d.name [] x e with
          | none => simp [hcf, ol] at hr
          | some fr =>
            cases hen : enter g { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a with
            | none => simp [hcf, hen, ol] at hr
            | some th' =>
              simp only [hcf, hen, ol, Option.bind_some, Option.map_some, Option.toList_some,
                List.mem_singleton] at hr
              subst hr
              obtain ⟨h1, h2⟩ := enter_pf hp hen
              refine ⟨h1, ?_⟩
              rw [h2]
              intro f' hf'
              rcases List.mem_cons.1 hf' with rfl | hf'
              · show pubFree fr.body = true
                rw [callFrame_body hcf]; exact hok.2
              · exact hstk f' hf'
        · simp at hr
      · simp at hr
    · simp at hr
  · -- new (records the allocation type; term and stack as for every other let)
    rename_i _ x a T e heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    simp only [List.mem_map] at hr
    obtain ⟨_, -, rfl⟩ := hr
    dsimp only
    split <;> exact ⟨hok.2, hstk⟩
  · -- every other let
    rename_i _ x op e _ _ _ heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    simp only [List.mem_map] at hr
    obtain ⟨_, -, rfl⟩ := hr
    exact ⟨hok.2, hstk⟩
  · -- split
    rename_i _ a x y e heq
    rw [heq] at hok
    split at hr
    · split at hr
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok, hstk⟩
      · simp at hr
    · simp at hr
  · -- unpack
    rename_i _ a i x e heq
    rw [heq] at hok
    split at hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok, hstk⟩
    · simp at hr
  · -- unpackT
    rename_i _ a α x e heq
    rw [heq] at hok
    split at hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok, hstk⟩
    · simp at hr
  · -- region
    rename_i _ a rn pn tn e heq
    rw [heq] at hok
    split at hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok, hstk⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok, hstk⟩
    · simp at hr
  · -- openPub
    rename_i _ a rn pn cn e heq
    rw [heq] at hok
    split at hr
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok, hstk⟩
    · simp at hr
  · -- case
    rename_i _ a x e₁ y e₂ heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · rename_i t u w ws hev
      simp only [List.mem_flatMap, List.mem_map] at hr
      obtain ⟨⟨s1, j, q⟩, -, ⟨s2, q'⟩, -, rfl⟩ := hr
      by_cases hj : j < (armsOf u).length
      · simp only [hj, ite_true]; exact ⟨hok.1, hstk⟩
      · simp only [hj, ite_false]; exact ⟨hok.2, hstk⟩
    · simp at hr
  · -- ifnull
    rename_i _ a e₁ y e₂ heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok.1, hstk⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hok.2, hstk⟩
      · simp at hr
    · simp at hr
  · -- parity
    rename_i _ a k ev od heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        refine ⟨?_, hstk⟩
        split
        · exact hok.1
        · exact hok.2
      · simp at hr
    · simp at hr
  · -- ifeq (numbers, or two thread-id references)
    rename_i _ a b yes no heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · split at hr <;>
        first
        | (simp only [List.mem_singleton] at hr
           subst hr
           refine ⟨?_, hstk⟩
           split
           · exact hok.1
           · exact hok.2)
        | simp at hr
    · simp at hr
  · -- cas
    rename_i _ acq rel w e v t ok fail heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_map] at hr
        obtain ⟨_, -, rfl⟩ := hr
        dsimp only
        split
        · exact ⟨hok.1, hstk⟩
        · exact ⟨hok.2, hstk⟩
      · simp at hr
    · simp at hr
  · -- casp
    rename_i _ acq rel w e0 e1 v0 v1 t ok fail heq
    rw [heq] at hok
    simp only [pubFree, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_map] at hr
        obtain ⟨_, -, rfl⟩ := hr
        dsimp only
        split
        · exact ⟨hok.1, hstk⟩
        · exact ⟨hok.2, hstk⟩
      · simp at hr
    · simp at hr
  · -- ret
    rename_i _ a heq
    split at hr
    · rename_i f rest _ ws hst _
      simp only [List.mem_singleton] at hr
      subst hr
      rw [hst] at hstk
      exact ⟨hstk f (List.mem_cons_self ..), fun f' hf' => hstk f' (List.mem_cons_of_mem _ hf')⟩
    · simp at hr
  · -- tail
    rename_i _ f is a ts heq
    cases hen : enter g th f ts a with
    | none => simp [hen, ol] at hr
    | some th' =>
      simp only [hen, ol, Option.map_some, Option.toList_some, List.mem_singleton] at hr
      subst hr
      obtain ⟨h1, h2⟩ := enter_pf hp hen
      exact ⟨h1, by rw [h2]; exact hstk⟩

/-! ## Along runs -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem pf_thread {i : Nat} {c c' : Cfg} (hp : ProgPubFree p) (h0 : RunPF c) (hc : c' ∈ threadSteps p k arch c i) :
    RunPF c' := by
  obtain ⟨th, r, hth, hr, -, -, e3, ho⟩ := TermStepper.threadSteps_upd hc
  intro j thj hj
  by_cases hji : j = i
  · subst hji
    rw [e3] at hj
    cases hj
    exact tstep_pf (g := gOf p k arch _ j) hp (h0 j th hth) hr
  · rw [ho j hji] at hj
    exact h0 j thj hj

theorem pf_prom {c : Cfg} {i : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} (h0 : RunPF c) :
    RunPF (promise c i a v w) := by
  cases hth : c.ths[i]? with
  | none =>
    have e : promise c i a v w = c := by simp only [promise, hth]
    rw [e]; exact h0
  | some th =>
    obtain ⟨-, hpj, -⟩ := TermStep.promise_inv (a := a) (v := v) (w := w) hth
    intro j thj hj
    by_cases hji : j = i
    · subst hji
      rw [hpj] at hj
      cases hj
      exact ⟨(h0 j th hth).term, (h0 j th hth).stk⟩
    · rw [TermStep.promise_other hji] at hj
      exact h0 j thj hj

/-- An uncertified extern move keeps `RunPF`: it only advances thread `i` past its `let`. -/
theorem pf_ext {c c' : Cfg} {i : Nat} (h0 : RunPF c) (hc : c' ∈ extSteps c i) : RunPF c' := by
  obtain ⟨th, x, n, a, e, rt, ws, rs, hth, ht, -, -, -, rfl⟩ := extSteps_elim hc
  have hT := h0 i th hth
  have hok := hT.term
  rw [ht] at hok
  simp only [pubFree, Bool.and_eq_true] at hok
  intro j thj hj
  by_cases hji : j = i
  · subst hji
    unfold extCfg curCfg at hj
    have hi : j < c.ths.size := (Array.getElem?_eq_some_iff.mp hth).1
    split at hj <;> (try split at hj) <;> simp [Array.set!, hi] at hj <;> subst hj <;>
      exact ⟨hok.2, hT.stk⟩
  · have e' : (extCfg c i th x n e ws rs).ths[j]? = c.ths[j]? := by
      unfold extCfg curCfg; split <;> (try split) <;> simp [Array.set!, Ne.symm hji]
    rw [e'] at hj
    exact h0 j thj hj

/-- **`RunPF` along every solo run** of a publish-free program. -/
theorem solo_pf {i : Nat} {c c1 : Cfg} (hp : ProgPubFree p) (h : Solo p k arch i c c1) : RunPF c → RunPF c1 := by
  induction h with
  | refl => exact id
  | thread hs _ ih => exact fun h0 => ih (pf_thread hp h0 hs)
  | prom a v w _ _ ih => exact fun h0 => ih (pf_prom h0)
  | ext hs _ ih => exact fun h0 => ih (pf_ext h0 hs)

/-- **A machine step keeps `RunPF`.** -/
theorem runPF_step {c1 c2 : Cfg} (hp : ProgPubFree p) (h0 : RunPF c1) (hs : Step p k arch c1 c2) : RunPF c2 := by
  cases hs with
  | thread i hc _ => exact pf_thread hp h0 hc
  | prom i a v w hi _ _ => exact pf_prom h0

/-- **A spawn keeps `RunPF`**: the parent continues with the `let`'s body,
the child runs a `tail`, with no stack. -/
theorem runPF_spawnStep {cap : Nat} {c c' : Cfg} (h : Spawn p k arch cap c c') (hc : RunPF c) : RunPF c' := by
  obtain ⟨i, x, f, a, T, ts, e, th, rt, ws, hth, ht, -, -, -, rfl⟩ := h.elim
  have hT := hc i th hth
  have hok := hT.term
  rw [ht] at hok
  simp only [pubFree, Bool.and_eq_true] at hok
  intro j th0 hj
  simp only [spawnCfg, spawnT] at hj
  rw [Array.getElem?_push] at hj
  split at hj
  · cases hj
    exact ⟨rfl, fun f hf => by simp [spawnKid] at hf⟩
  · rcases TermViewInv.getElem?_set!_cases hj with rfl | hj
    · exact ⟨hok.2, hT.stk⟩
    · exact hc j th0 hj

/-- **`RunPF` at every configuration reachable from `cs`** by machine steps and `Sp` steps. -/
def RunPFR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (cs : Cfg) : Prop :=
  ∀ {c : Cfg}, StepsG p k arch Sp cs c → RunPF c

/-- **`RunPF` along every run** of a publish-free program (the `Sp` arm is the caller's). -/
theorem runPFR_of {Sp : Cfg → Cfg → Prop} {cs : Cfg} (hp : ProgPubFree p)
    (hSp : ∀ c c', Sp c c' → RunPF c → RunPF c') (h : RunPF cs) : RunPFR p k arch Sp cs :=
  fun hr => stepsG_pres (fun _ _ hs hv => runPF_step hp hv hs) hSp hr h

/-- `RunPFR` with spawns. -/
theorem runPFR_spawn {cap : Nat} {cs : Cfg} (hp : ProgPubFree p) (h : RunPF cs) :
    RunPFR p k arch (Spawn p k arch cap) cs :=
  runPFR_of hp (fun _ _ hs h => runPF_spawnStep hs h) h

/-- `RunPFR` without spawns. -/
theorem runPFR_bot {cs : Cfg} (hp : ProgPubFree p) (h : RunPF cs) : RunPFR p k arch (fun _ _ => False) cs :=
  runPFR_of hp (fun _ _ hf _ => hf.elim) h

end

/-- **The start condition for the `spawn` shape**: every initial thread runs
`tail f [] (var "a") ts` with no stack (`TermInit.runDRF_spawn`'s shape). -/
theorem runPF_init {c0 : Cfg}
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → ∃ (f : String) (is : List String) (a : At) (ts : List Ty),
      th.term = .tail f is a ts ∧ th.stack = []) : RunPF c0 := by
  intro i th hth
  obtain ⟨f, is, a, ts, h1, h2⟩ := h i th hth
  exact ⟨by rw [h1]; rfl, by rw [h2]; intro f hf; cases hf⟩

/-! ## The windows -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : Cfg → Cfg → Prop}

/-- **At a configuration without `publish`, `NoHoldPubN` holds** (its premise
asks for a thread at `let x = publish a in e`). -/
theorem noHoldPubN_of {E0 E1 : TEnv} {i : Nat} {c : Cfg} (h : RunPF c) : NoHoldPubN p k arch E0 E1 i c := by
  intro th hth _ _ _ _ _ _ _ _ _ _ _ _ _ _ x a e _ _ _ ht _ _ _
  have hpf := (h i th hth).term
  rw [ht] at hpf
  simp [pubFree, isPublish] at hpf

/-- **`CertWinCNX` holds for a publish-free program** from a `RunPF` start. -/
theorem certWinCNX_of_noPublish (hp : ProgPubFree p) (h0 : RunPFR p k arch Sp c0) :
    CertWinCNX p k arch Sp Init MintOK c0 :=
  fun X _ _ _ h1 _ => noHoldPubN_of (solo_pf hp h1 (h0 X.run))

/-- **`CertWinPNX` holds for a publish-free program** from a `RunPF` start. -/
theorem certWinPNX_of_noPublish (hp : ProgPubFree p) (h0 : RunPFR p k arch Sp c0) :
    CertWinPNX p k arch Sp Init MintOK c0 :=
  fun X => ⟨fun _ _ _ h1 _ => noHoldPubN_of (solo_pf hp h1 (pf_prom (h0 X.run))),
    fun _ _ _ _ _ _ _ h1 _ => noHoldPubN_of (solo_pf hp h1 (pf_prom (h0 X.run)))⟩

/-- `CertWinCN` (runs without spawns) for a publish-free program. -/
theorem certWinCN_of_noPublish (hp : ProgPubFree p) (h0 : RunPF c0) : CertWinCN p k arch Init MintOK c0 :=
  fun X => certWinCNX_of_noPublish (Sp := fun _ _ => False) hp (runPFR_bot hp h0) X.toX

/-- `CertWinPN` (runs without spawns) for a publish-free program. -/
theorem certWinPN_of_noPublish (hp : ProgPubFree p) (h0 : RunPF c0) : CertWinPN p k arch Init MintOK c0 :=
  fun X => certWinPNX_of_noPublish (Sp := fun _ _ => False) hp (runPFR_bot hp h0) X.toX

end

/-! ## Typing -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}

/-- **The obligations with spawns for a publish-free program**: the windows
from `ProgPubFree` and `RunPF c0`; the checker, the scope check and the
initial scope invariant remain. -/
theorem obligationsFX_of_noPublish (hck : checkProg p = .ok ()) (hsc : TermScope.ProgScopeOKW p = true)
    (hrs : TermScope.RunScope c0) (hp : ProgPubFree p) (hpf : RunPF c0) :
    ObligationsFX p k arch (Spawn p k arch c0.cap) Init (fun _ => True) c0 :=
  ⟨hck, hsc, hrs⟩

/-- **Every thread is typed along every run with spawns** of a publish-free
program (`machine_tokens_main_spawn`'s per-thread conjunct). -/
theorem srcTyped_spawn_of_noPublish (hck : checkProg p = .ok ()) (hsc : TermScope.ProgScopeOKW p = true)
    (hrs : TermScope.RunScope c0) (hp : ProgPubFree p) (hpf : RunPF c0) (hk : k.storeDepRts = true)
    (hS : A9SpawnFinal.StartOKX p k arch Init c0) {c : Cfg} (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) :
    SrcTyped p c := by
  obtain ⟨_, _, _, _, _, _, -, -, -, hth⟩ :=
    SpawnArmZ.machine_tokens_main_spawn (obligationsFX_of_noPublish hck hsc hrs hp hpf) hk hS hr
  intro i th h
  obtain ⟨_, _, _, _, _, _, -, -, ht, hf, -⟩ := hth i th h
  exact threadTyped_of ht hf

/-- **The obligations without spawns for a publish-free program.** -/
theorem obligationsF_of_noPublish (hck : checkProg p = .ok ()) (hsc : TermScope.ProgScopeOKW p = true)
    (hrs : TermScope.RunScope c0) (hp : ProgPubFree p) (hpf : RunPF c0) :
    ObligationsF p k arch Init (fun _ => True) c0 :=
  ⟨hck, hsc, hrs⟩

/-- **Every thread is typed along every run without spawns** of a
publish-free program (`machine_tokens_mainF`'s per-thread conjunct). -/
theorem srcTyped_mainF_of_noPublish (hck : checkProg p = .ok ()) (hsc : TermScope.ProgScopeOKW p = true)
    (hrs : TermScope.RunScope c0) (hp : ProgPubFree p) (hpf : RunPF c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    SrcTyped p c := by
  obtain ⟨_, _, _, _, _, _, -, -, -, hth⟩ :=
    machine_tokens_mainF (obligationsF_of_noPublish hck hsc hrs hp hpf) hk h0 hr
  intro i th h
  obtain ⟨_, _, _, _, _, _, -, -, ht, hf, -⟩ := hth i th h
  exact threadTyped_of ht hf

end

/-! ## Tests (D5(b)) -/

/-- A publish-free code block: it allocates and returns. -/
def allocD : Decl where
  name := "alloc"; idx := []; arg := "x"
  argTy := .int
  retTy := .int
  body := lets [("p", .new (v "x") (some .int))] (.ret (v "x"))

/-- A one-block program without `publish` passes the check. -/
theorem progPubFree_alloc : ProgPubFree [allocD] := by decide

/-- WeakCore's `leakD` publishes, so a program containing it fails the check. -/
theorem not_progPubFree_leak : ¬ ProgPubFree [allocD, leakD] := by decide

/-- A `publish` under a branch is found. -/
theorem not_pubFree_branch : pubFree (.ifeq (.lit 0) (.lit 0) (.ret .unit) (lets [("s", .publish (v "q"))] (.ret .unit))) = false := by
  decide

end Scc.Sem.PubFree
