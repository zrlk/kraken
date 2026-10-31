/-
# TermLocal — soundness of the `local` window rule on the machine (L5)

`Robust.walk` (the second pass of `checkProgL`) enforces that a held token of
a `local` protocol lives in a straight-line window of one block.  This file
gives that rule machine content:

* §1 `tstep_shape`: a step at a term with no `call`/`callc`/`tail`/`ret` at its
  head moves to an immediate subterm, keeps the stack, and extends the
  environment at the front; `tstep_cas`: the entering `cas` binds the (erased)
  token at the front.
* §2 `WinW`: `Robust.walk`'s acceptance as an inductive predicate;
  `walkT_sound` / `localDeclT_sound` (`Robust.walk` is structural, so its
  equations unfold, and `accepts (checkProgL p)` yields `WinW`).
* §3 `local_confined`: in a window, a step is the leaving store or stays in
  the window (suffix of the body, same stack, token binding kept, a token
  still held by the checker's context).
* §4 `local_bounded_release`: within `esize body` own steps the holder reaches
  the leaving store.

Hypothesis: `Follows` (stage A: at a non-`let` term the machine takes a branch
whose checker context still holds the token).

Build: LEAN_PATH=build lean -o build/TermLocal.olean TermLocal.lean
-/
import WeakCore.Robust
import WeakCore.TermRun
open CoreLang CoreTerm TermRun

namespace TermLocal

/-! ## §1 Control shape of a straight-line step -/

/-- Constructors of a term. -/
def esize : Expr → Nat
  | .let_ _ _ b | .split _ _ _ b | .unpack _ _ _ b | .unpackT _ _ _ b | .region _ _ _ _ b
  | .openPub _ _ _ _ b => esize b + 1
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂
  | .cas _ _ _ _ _ _ e₁ e₂ | .casp _ _ _ _ _ _ _ _ e₁ e₂ => esize e₁ + esize e₂ + 1
  | .ret _ | .tail .. => 1

theorem esize_pos (e : Expr) : 0 < esize e := by
  cases e <;> simp [esize]

theorem esize_subs {e s : Expr} (h : s ∈ Robust.subs e) : esize s < esize e := by
  cases e <;> simp only [Robust.subs, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    (try rcases h with rfl | rfl) <;> (try subst h) <;> simp only [esize] <;> omega

open Robust (isCallOp)

/-- No `call`, `callc`, `tail` or `ret` at the head. -/
def straight : Expr → Bool
  | .let_ _ op _ => !isCallOp op
  | .ret _ | .tail .. => false
  | _ => true

theorem withS_term (th : TTh) (s : St) : (withS th s).term = th.term := rfl
theorem withS_env (th : TTh) (s : St) : (withS th s).env = th.env := rfl
theorem withS_stack (th : TTh) (s : St) : (withS th s).stack = th.stack := rfl

theorem tstep_let_gen {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {x : String} {op : Op} {b : Expr} (hterm : th.term = .let_ x op b) (hc : isCallOp op = false)
    (hnn : ∀ a T, op ≠ .new a T := by intro _ _ h; cases h) :
    tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map
      fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := b, env := (x, t, ws) :: th.env } s') := by
  cases op <;> first | (simp [isCallOp] at hc; done) | exact absurd rfl (hnn _ _) | simp [tstep, hterm]

/-- The shape of a step: into an immediate subterm, the stack kept, the
environment extended at the front. -/
def Shape (th th' : TTh) : Prop :=
  th'.term ∈ Robust.subs th.term ∧ th'.stack = th.stack ∧ ∃ pre, th'.env = pre ++ th.env

theorem tstep_shape {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {r : WeakMem.Memory × List WeakMem.Ts × TTh}
    (hs : straight th.term = true) (hr : r ∈ tstep g mem pairs th) : Shape th r.2.2 := by
  obtain ⟨m, ps, th'⟩ := r
  cases hterm : th.term with
  | let_ x op b =>
      rw [hterm] at hs
      simp only [straight, Bool.not_eq_true'] at hs
      by_cases hn : ∃ a T, op = .new a T
      · obtain ⟨a, T, rfl⟩ := hn
        obtain ⟨s', t, ws, -, tys, he⟩ := TermRun.tstep_new_mem hterm hr
        cases he
        exact ⟨by simp [Robust.subs, withS_term, hterm], rfl, [(x, t, ws)], rfl⟩
      rw [tstep_let_gen hterm hs (fun a T h => hn ⟨a, T, h⟩)] at hr
      simp only [List.mem_map] at hr
      obtain ⟨⟨s', t, ws⟩, -, he⟩ := hr
      cases he
      exact ⟨by simp [Robust.subs, withS_term, hterm], rfl, [(x, t, ws)], rfl⟩
  | ret a => rw [hterm] at hs; simp [straight] at hs
  | tail f is a ts => rw [hterm] at hs; simp [straight] at hs
  | _ =>
      simp only [tstep, hterm] at hr
      repeat' split at hr
      all_goals first
        | (simp at hr; done)
        | (simp only [List.mem_singleton, Prod.mk.injEq] at hr
           obtain ⟨-, -, rfl⟩ := hr
           exact ⟨by simp [Robust.subs, hterm, withS], rfl,
             by first | exact ⟨[], rfl⟩ | exact ⟨[_], rfl⟩ | exact ⟨[_, _], rfl⟩⟩)
        | (simp only [List.mem_map, Prod.mk.injEq] at hr
           obtain ⟨_, -, -, -, rfl⟩ := hr
           split <;> exact ⟨by simp [Robust.subs, hterm, withS], rfl,
             by first | exact ⟨[], rfl⟩ | exact ⟨[_], rfl⟩⟩)
        | (simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hr
           obtain ⟨_, -, _, -, -, -, rfl⟩ := hr
           split <;> exact ⟨by simp [Robust.subs, hterm, withS], rfl, ⟨[_], rfl⟩⟩)

/-- The entering `cas`: its success branch binds the (erased) token at the
front of the environment; the stack is untouched. -/
theorem tstep_cas {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {r : WeakMem.Memory × List WeakMem.Ts × TTh} {acq rel : Bool} {w e v : At} {t : String}
    {ok fail : Expr} (hterm : th.term = .cas acq rel w e v t ok fail) (hr : r ∈ tstep g mem pairs th) :
    ((r.2.2.term = ok ∧ r.2.2.env = (t, .unit, []) :: th.env) ∨
      (r.2.2.term = fail ∧ r.2.2.env = th.env)) ∧ r.2.2.stack = th.stack := by
  obtain ⟨m, ps, th'⟩ := r
  simp only [tstep, hterm] at hr
  repeat' split at hr
  all_goals first
    | (simp at hr; done)
    | (simp only [List.mem_map, Prod.mk.injEq] at hr
       obtain ⟨_, -, -, -, rfl⟩ := hr
       split
       · exact ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩
       · exact ⟨Or.inr ⟨rfl, rfl⟩, rfl⟩)

/-! ## §2 The window, as `Robust.walk` checks it

`WinW p cx e` is `Robust.walk`'s acceptance, clause for clause, as an inductive predicate: at a `let`,
no call while a local token is held, and a held token leaves the context only
by a store on it or by being restructured into the bound variable (`goneOK`);
at `ret`/`tail`, nothing held; elsewhere, every branch whose checker context
is known. -/

open Robust (localHolders goneOK seqM onBr)

def isOther : Expr → Bool
  | .let_ .. | .ret _ | .tail .. => false
  | _ => true

inductive WinW (p : Prog) : Cx → Expr → Prop
  | let_ {cx : Cx} {x : String} {op : Op} {b : Expr} :
      (isCallOp op = true → localHolders cx = []) →
      (∀ c', Scope.branches p cx (.let_ x op b) = [some c'] → goneOK cx c' x op = true) →
      (∀ c', Scope.branches p cx (.let_ x op b) = [some c'] → WinW p c' b) →
      WinW p cx (.let_ x op b)
  | ret {cx : Cx} {a : At} : localHolders cx = [] → WinW p cx (.ret a)
  | tail {cx : Cx} {f : String} {is : List String} {a : At} {ts : List Ty} :
      localHolders cx = [] → WinW p cx (.tail f is a ts)
  | other {cx : Cx} {e : Expr} : isOther e = true →
      (∀ (k : Nat) (c : Cx) (s : Expr), (Scope.branches p cx e)[k]? = some (some c) →
        (Robust.subs e)[k]? = some s → WinW p c s) →
      WinW p cx e

theorem winW_straight {p : Prog} {cx : Cx} {e : Expr} (hw : WinW p cx e)
    (hh : localHolders cx ≠ []) : straight e = true := by
  cases hw with
  | let_ hc _ _ =>
      simp only [straight, Bool.not_eq_true']
      exact Bool.eq_false_iff.mpr fun h => hh (hc h)
  | ret h0 => exact absurd h0 hh
  | tail h0 => exact absurd h0 hh
  | other ho _ => cases e <;> simp_all [isOther, straight]

theorem winW_other {p : Prog} {cx : Cx} {e : Expr} (hw : WinW p cx e) (ho : isOther e = true) :
    ∀ (k : Nat) (c : Cx) (s : Expr), (Scope.branches p cx e)[k]? = some (some c) →
      (Robust.subs e)[k]? = some s → WinW p c s := by
  cases hw with
  | other _ h => exact h
  | _ => simp [isOther] at ho

/-- At a checked `let` inside a window: the body's context, and either a token
is still held or the `let` was a store on the last one. -/
theorem winW_let {p : Prog} {cx : Cx} {x : String} {op : Op} {b : Expr}
    (hw : WinW p cx (.let_ x op b)) (hh : localHolders cx ≠ [])
    (hc : CoreTerm.check p cx (.let_ x op b) = .ok ()) :
    ∃ c, checkOp p cx x op = .ok c ∧ CoreTerm.check p c b = .ok () ∧ WinW p c b ∧
      (localHolders c ≠ [] ∨ ∃ rel a v z, op = .store rel a v (some (.var z)) ∧
        z ∈ localHolders cx ∧ localHolders c = []) := by
  cases hco : checkOp p cx x op with
  | error msg => simp [CoreTerm.check_let, hco, bind, Except.bind] at hc
  | ok c =>
      have hcb : CoreTerm.check p c b = .ok () := by simpa [CoreTerm.check_let, hco, bind, Except.bind] using hc
      have hbr : Scope.branches p cx (.let_ x op b) = [some c] := by
        simp [Scope.branches, hco, Except.toOption]
      cases hw with
      | other ho _ => simp [isOther] at ho
      | let_ _ hk hk' =>
          have hg := hk c hbr
          have hwb := hk' c hbr
          refine ⟨c, rfl, hcb, hwb, ?_⟩
          by_cases hc' : localHolders c = []
          · right
            cases hhd : localHolders cx with
            | nil => exact absurd hhd hh
            | cons y ys =>
                simp only [goneOK, hc', hhd] at hg
                cases op <;> simp at hg
                rename_i rel a v tok _
                rcases tok with _ | ⟨_ | _ | z⟩ <;> simp at hg
                obtain ⟨rfl, -⟩ := hg
                exact ⟨rel, a, v, y, rfl, List.mem_cons_self, hc'⟩
          · exact Or.inl hc'

/-! ### `walk`'s acceptance is `WinW`

`Robust.walk` is structural (one arm per constructor), so `walkT_sound` can
unfold it: its acceptance is `WinW`, and `local_confined` follows from
`accepts (checkProgL p)` directly. -/

#guard [Robust.winD, Robust.winPairD].all fun d => accepts (Robust.localDecl Robust.localLib d)
#guard [Robust.winCallD, Robust.lockLD, Robust.winStoreD].all fun d =>
  !accepts (Robust.localDecl Robust.localLib d)

theorem seqM_ok {a b : M Unit} (h : seqM a b = .ok ()) : a = .ok () ∧ b = .ok () := by
  cases a with
  | ok u => exact ⟨rfl, h⟩
  | error e => simp [seqM] at h

theorem onBr_ok {o : Option (Option Cx)} {f : Cx → M Unit} (h : onBr o f = .ok ()) :
    ∀ c, o = some (some c) → f c = .ok () := by
  intro c hc
  subst hc
  exact h

theorem winW_one {p : Prog} {cx : Cx} {e b : Expr} (ho : isOther e = true)
    (hs : Robust.subs e = [b])
    (h1 : ∀ c, (Scope.branches p cx e)[0]? = some (some c) → WinW p c b) : WinW p cx e := by
  refine .other ho fun k c s hb hk => ?_
  rw [hs] at hk
  cases k with
  | zero => simp at hk; subst hk; exact h1 c hb
  | succ k => simp at hk

theorem winW_two {p : Prog} {cx : Cx} {e e₁ e₂ : Expr} (ho : isOther e = true)
    (hs : Robust.subs e = [e₁, e₂])
    (h1 : ∀ c, (Scope.branches p cx e)[0]? = some (some c) → WinW p c e₁)
    (h2 : ∀ c, (Scope.branches p cx e)[1]? = some (some c) → WinW p c e₂) : WinW p cx e := by
  refine .other ho fun k c s hb hk => ?_
  rw [hs] at hk
  match k, hk with
  | 0, hk => simp at hk; subst hk; exact h1 c hb
  | 1, hk => simp at hk; subst hk; exact h2 c hb
  | k + 2, hk => simp at hk

/-- `Robust.walk`'s acceptance is `WinW`. -/
theorem walkT_sound {p : Prog} {bn : String} :
    ∀ (e : Expr) (cx : Cx), Robust.walk p bn cx e = .ok () → WinW p cx e := by
  intro e
  induction e with
  | let_ x op b ih =>
      intro cx h
      simp only [Robust.walk] at h
      split at h
      · simp at h
      · rename_i hcall
        refine .let_ (fun hc => ?_) (fun c' hb => ?_) (fun c' hb => ?_)
        · simpa [hc] using hcall
        · rw [hb] at h
          dsimp only at h
          split at h
          · assumption
          · simp at h
        · rw [hb] at h
          dsimp only at h
          split at h
          · exact ih c' h
          · simp at h
  | ret a =>
      intro cx h
      simp only [Robust.walk] at h
      split at h
      · rename_i he
        exact .ret (List.isEmpty_iff.mp he)
      · simp at h
  | tail f is a ts =>
      intro cx h
      simp only [Robust.walk] at h
      split at h
      · rename_i he
        exact .tail (List.isEmpty_iff.mp he)
      · simp at h
  | split _ _ _ _ ih | unpack _ _ _ _ ih | unpackT _ _ _ _ ih | region _ _ _ _ _ ih
  | openPub _ _ _ _ _ ih =>
      intro cx h
      exact winW_one rfl rfl fun c hc => ih c (onBr_ok h c hc)
  | case _ _ _ _ _ ih₁ ih₂ | ifnull _ _ _ _ ih₁ ih₂ | parity _ _ _ _ ih₁ ih₂
  | ifeq _ _ _ _ ih₁ ih₂ | cas _ _ _ _ _ _ _ _ ih₁ ih₂ | casp _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      intro cx h
      obtain ⟨h1, h2⟩ := seqM_ok h
      exact winW_two rfl rfl (fun c hc => ih₁ c (onBr_ok h1 c hc)) (fun c hc => ih₂ c (onBr_ok h2 c hc))

/-- What `Robust.localDecl` accepts: the window rule from the block's start. -/
theorem localDeclT_sound {p : Prog} {d : Decl} (h : Robust.localDecl p d = .ok ()) :
    WinW p (Scope.start d) d.body := by
  cases h1 : Robust.hasLocalTok d.argTy <;> cases h2 : Robust.hasLocalTok d.retTy <;>
    simp [Robust.localDecl, h1, h2] at h <;> first
      | exact walkT_sound _ _ h
      | (cases h; done)

theorem forM_ok {f : Decl → M Unit} :
    ∀ (l : List Decl), l.forM f = .ok () → ∀ d ∈ l, f d = .ok ()
  | [], _, d, hd => by simp at hd
  | x :: xs, h, d, hd => by
    cases hx : f x with
    | error e => simp [List.forM, hx] at h; cases h
    | ok u =>
      simp [List.forM, hx] at h
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hx
      · exact forM_ok xs h d hd
/-- The checker's verdict gives every block's window: `accepts (checkProgL p)`
implies `WinW` at the start of each declaration's body. -/
theorem checkProgL_window {p : Prog} (h : accepts (Robust.checkProgL p) = true) :
    ∀ d ∈ p, WinW p (Scope.start d) d.body := by
  intro d hd
  have hok : Robust.checkProgL p = .ok () := by
    unfold accepts at h; split at h <;> simp_all
  have h1 := forM_ok p hok d hd
  simp only [Robust.checkDeclL] at h1
  cases hc : checkDecl p d with
  | error e => rw [hc] at h1; cases h1
  | ok u => rw [hc] at h1; exact localDeclT_sound h1

/-! ## §3 Confinement -/

/-- `Suffix s body`: `s` is reached from `body` through immediate subterms. -/
inductive Suffix : Expr → Expr → Prop
  | refl (e : Expr) : Suffix e e
  | sub {e s b : Expr} : s ∈ Robust.subs e → Suffix e b → Suffix s b

theorem Suffix.esize_le {s b : Expr} (h : Suffix s b) : esize s ≤ esize b := by
  induction h with
  | refl => exact Nat.le_refl _
  | sub hs _ ih => exact Nat.le_trans (Nat.le_of_lt (esize_subs hs)) ih

/-- A thread inside the window entered with stack `stk` and environment
`env0` (the environment right after the entering `cas`, which binds the
token), whose body is `body`: its term is a suffix of `body`, its stack is
`stk` (no frame pushed or popped), its environment extends `env0` at the
front, and at its term some checker context holds a local token, accepts the
term (`check`) and passes the window rule (`WinW`). -/
structure InWin (p : Prog) (body : Expr) (stk : List Frame) (env0 : Env) (th : TTh) : Prop where
  suf : Suffix th.term body
  stack : th.stack = stk
  env : ∃ pre, th.env = pre ++ env0
  win : ∃ cx, WinW p cx th.term ∧ localHolders cx ≠ [] ∧ CoreTerm.check p cx th.term = .ok ()

/-- The start of a window: right after the entering `cas`'s success. -/
theorem InWin.start {p : Prog} {th : TTh} {cx : Cx} (hw : WinW p cx th.term)
    (hh : localHolders cx ≠ []) (hc : CoreTerm.check p cx th.term = .ok ()) :
    InWin p th.term th.stack th.env th :=
  ⟨.refl _, rfl, ⟨[], rfl⟩, cx, hw, hh, hc⟩

/-- The token bound by the entering `cas` stays in the current environment. -/
theorem InWin.tok_mem {p : Prog} {body : Expr} {stk : List Frame} {t : String} {env0 : Env}
    {th : TTh} (h : InWin p body stk ((t, .unit, []) :: env0) th) : (t, .unit, []) ∈ th.env := by
  obtain ⟨pre, he⟩ := h.env
  rw [he]
  exact List.mem_append_right _ List.mem_cons_self

/-- Entering: the success step of a `cas` at a checked, window-correct term
whose success branch's checker context holds a local token starts a window on
that branch, with the token bound at the front of the environment. -/
theorem inWin_enter {p : Prog} {th : TTh} {cx c : Cx} {acq rel : Bool} {w e v : At} {t : String}
    {ok fail : Expr} {r : WeakMem.Memory × List WeakMem.Ts × TTh}
    (hterm : th.term = .cas acq rel w e v t ok fail) (hw : WinW p cx th.term)
    (hb : (Scope.branches p cx th.term)[0]? = some (some c)) (hh : localHolders c ≠ [])
    (hc : CoreTerm.check p c ok = .ok ()) (hstk : r.2.2.stack = th.stack)
    (hok : r.2.2.term = ok ∧ r.2.2.env = (t, .unit, []) :: th.env) :
    InWin p ok th.stack ((t, .unit, []) :: th.env) r.2.2 := by
  have hw' : WinW p c ok := by
    rw [hterm] at hw hb
    exact winW_other hw rfl 0 c ok hb rfl
  refine ⟨?_, hstk, ⟨[], hok.2⟩, c, ?_, hh, ?_⟩
  · rw [hok.1]; exact .refl _
  · rw [hok.1]; exact hw'
  · rw [hok.1]; exact hc

/-- No `call`, `callc`, `tail` or `ret` while in the window. -/
theorem InWin.straight {p : Prog} {body : Expr} {stk : List Frame} {env0 : Env} {th : TTh}
    (h : InWin p body stk env0 th) : straight th.term = true := by
  obtain ⟨cx, hw, hh, -⟩ := h.win
  exact winW_straight hw hh

/-- **Stage-A fact, taken as a hypothesis** for a step at a non-`let` term:
the branch the machine takes is one whose checker context is known, still
holds a local token, and accepts the branch.  (For `case` the context of the
arm the value does not inhabit may hold nothing — `Tok + Unit`'s right arm —
so this is a fact about the run, from the runtime typing `FInv`, not about the
text.) -/
def Follows (p : Prog) (th th' : TTh) : Prop :=
  isOther th.term = true → ∀ cx, WinW p cx th.term → localHolders cx ≠ [] →
    CoreTerm.check p cx th.term = .ok () →
    ∃ (k : Nat) (c : Cx), (Robust.subs th.term)[k]? = some th'.term ∧
      (Scope.branches p cx th.term)[k]? = some (some c) ∧ localHolders c ≠ [] ∧
      CoreTerm.check p c th'.term = .ok ()

/-- The leaving store: a `store` on a held local token after which the
checker's context holds none. -/
def Exits (p : Prog) (th : TTh) : Prop :=
  ∃ (cx : Cx) (x : String) (rel : Bool) (a v : At) (z : String) (b : Expr) (c : Cx),
    th.term = .let_ x (.store rel a v (some (.var z))) b ∧ WinW p cx th.term ∧
    z ∈ localHolders cx ∧ checkOp p cx x (.store rel a v (some (.var z))) = .ok c ∧
    localHolders c = []

/-- **Window confinement.**  A step of a thread in the window either is the
leaving store, or keeps it in the window: the term moves to an immediate
subterm (still a suffix of the window's body, `esize` strictly smaller), no
frame is pushed or popped, the environment only grows at the front (so the
token's binding stays), and a checker context still holds a local token. -/
theorem local_confined {p : Prog} {body : Expr} {stk : List Frame} {env0 : Env} {th : TTh}
    {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts}
    {r : WeakMem.Memory × List WeakMem.Ts × TTh}
    (h : InWin p body stk env0 th) (hr : r ∈ tstep g mem pairs th) (hf : Follows p th r.2.2) :
    (InWin p body stk env0 r.2.2 ∧ esize r.2.2.term < esize th.term) ∨ Exits p th := by
  obtain ⟨hsub, hstk, pre, henv⟩ := tstep_shape h.straight hr
  obtain ⟨cx, hw, hh, hc⟩ := h.win
  obtain ⟨pre0, h0⟩ := h.env
  have hsuf : Suffix r.2.2.term body := .sub hsub h.suf
  have hst : r.2.2.stack = stk := hstk.trans h.stack
  have hen : ∃ pre, r.2.2.env = pre ++ env0 := ⟨pre ++ pre0, by rw [henv, h0, List.append_assoc]⟩
  have hlt := esize_subs hsub
  cases ho : isOther th.term
  · have hs := h.straight
    cases hterm : th.term with
    | let_ x op b =>
        rw [hterm] at hw hc hsub
        have hb : r.2.2.term = b := by simpa [Robust.subs] using hsub
        obtain ⟨c, hco, hcb, hwb, hor⟩ := winW_let hw hh hc
        rcases hor with hc' | ⟨rel, a, v, z, rfl, hz, hc'⟩
        · exact Or.inl ⟨⟨hsuf, hst, hen, c, by rw [hb]; exact hwb, hc', by rw [hb]; exact hcb⟩,
            by rw [← hterm]; exact hlt⟩
        · exact Or.inr ⟨cx, x, rel, a, v, z, b, c, hterm, by rw [hterm]; exact hw, hz, hco, hc'⟩
    | ret a => rw [hterm] at hs; simp [straight] at hs
    | tail f is a ts => rw [hterm] at hs; simp [straight] at hs
    | _ => rw [hterm] at ho; simp [isOther] at ho
  · obtain ⟨k, c, hk, hb, hc', hcc⟩ := hf ho cx hw hh hc
    exact Or.inl ⟨⟨hsuf, hst, hen, c, winW_other hw ho k c _ hb hk, hc', hcc⟩, hlt⟩

/-! ## §4 Bounded release -/

/-- `n` own steps of a thread (`tstep`, at any memory: other threads' steps
and promise steps do not touch the term, environment or stack), each meeting
`Follows`. -/
inductive Run (p : Prog) : Nat → TTh → TTh → Prop
  | refl (th : TTh) : Run p 0 th th
  | step {n : Nat} {th th' th'' : TTh} (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts)
      (m : WeakMem.Memory) (ps : List WeakMem.Ts) :
      (m, ps, th') ∈ tstep g mem pairs th → Follows p th th' → Run p n th' th'' →
      Run p (n + 1) th th''

theorem bounded_aux {p : Prog} {body : Expr} {stk : List Frame} {env0 : Env} :
    ∀ {n : Nat} {th th' : TTh}, InWin p body stk env0 th → Run p n th th' → esize th.term ≤ n →
      ∃ m, m < n ∧ ∃ thm, Run p m th thm ∧ InWin p body stk env0 thm ∧ Exits p thm := by
  intro n th th' h hr hn
  induction hr with
  | refl th => exact absurd hn (Nat.not_le_of_lt (esize_pos _))
  | step g mem pairs m ps hst hf hrest ih =>
      rcases local_confined h hst hf with ⟨h1, hlt⟩ | hex
      · dsimp only at hlt h1
        obtain ⟨m', hm', thm, hrm, hin, hex⟩ := ih h1 (by omega)
        exact ⟨m' + 1, by omega, thm, .step g mem pairs m ps hst hf hrm, hin, hex⟩
      · exact ⟨0, by omega, _, .refl _, h, hex⟩

/-- **Bounded release.**  A thread in a window whose body has `N = esize body`
constructors, taking `n ≥ N` own steps, reaches the leaving store after fewer
than `n` of them (so its next own step is that store): the window has no loop,
since each step consumes a constructor. -/
theorem local_bounded_release {p : Prog} {body : Expr} {stk : List Frame} {env0 : Env}
    {n : Nat} {th th' : TTh} (h : InWin p body stk env0 th) (hr : Run p n th th')
    (hn : esize body ≤ n) :
    ∃ m, m < n ∧ ∃ thm, Run p m th thm ∧ InWin p body stk env0 thm ∧ Exits p thm :=
  bounded_aux h hr (Nat.le_trans h.suf.esize_le hn)

end TermLocal

#print axioms TermLocal.tstep_shape
#print axioms TermLocal.tstep_cas
#print axioms TermLocal.walkT_sound
#print axioms TermLocal.localDeclT_sound
#print axioms TermLocal.winW_let
#print axioms TermLocal.inWin_enter
#print axioms TermLocal.local_confined
#print axioms TermLocal.local_bounded_release
#print axioms TermLocal.checkProgL_window
