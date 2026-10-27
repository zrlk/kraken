import WeakCore.TermCohLe
import WeakCore.TermNoHold
import WeakCore.TermScope
import WeakCore.TermPlantF
import WeakCore.TermDPlus

/-!
# TermCertScope: the scope half of the certificate run facts (option (3), with endCx (iv))

`TermCohLe.CertRunC` / `TermNoHold.CertRunP` ask, along every certified solo run of the
stepper, for `ScopeAt ∧ NoHoldPub`.  Here they are split:

* `CertScopeC` / `CertScopeP` (the `ScopeAt` half) are **theorems** for a program passing
  `ProgScopeOK` from a `RunScope` start: `RunScope` holds along solo runs (`solo_drf`), and at a
  `drf` frame every typing is in scope (`scope_termV`); with `opOK` excluding the ticket
  operations, the frame-only alternative `StepScopeR` is a capability term (`scopeD_of`).
* `CertWinC` / `CertWinP` (the `NoHoldPub` half) stay named run facts (the NoHold (a)/(b)
  cycle).

`certRunC_of` / `certRunP_of` rebuild the conjunction, so every consumer is unchanged.
-/

namespace TermCertScope
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermTyped TermScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## `RunScope` along solo runs -/

theorem drf_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScope c) (hc : c' ∈ threadSteps p k arch c i) : RunScope c' := by
  obtain ⟨th, r, hth, hr, -, -, e3, ho⟩ := TermStepper.threadSteps_upd hc
  intro j thj hj
  by_cases hji : j = i
  · subst hji
    rw [e3] at hj
    cases hj
    exact tstep_drf (g := gOf p k arch _ j) hp (h0 j th hth) hr
  · rw [ho j hji] at hj
    exact h0 j thj hj

theorem drf_prom {c : Cfg} {i : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} (h0 : RunScope c) :
    RunScope (promise c i a v w) := by
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
      exact ⟨(h0 j th hth).ok, (h0 j th hth).σs, (h0 j th hth).env, (h0 j th hth).stk⟩
    · rw [TermStep.promise_other hji] at hj
      exact h0 j thj hj

/-- The extern move keeps `RunScope` (the continuation of a scoped `let`, one more binding). -/
theorem drf_ext {c c' : Cfg} {i : Nat} (h0 : TermScope.RunScope c) (hs : c' ∈ extSteps c i) :
    TermScope.RunScope c' := by
  rcases extSteps_shape hs with ⟨th, hth, ⟨x, n, a, e, evs, rs, hterm, -, -, rfl⟩ | ⟨x, a, e, l, hterm, -, rfl⟩⟩ <;>
  · intro j t hj
    rcases set_get_cases hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
    · obtain ⟨hok, hσs, he, hstk⟩ := h0 _ th hth
      rw [hterm] at hok he
      simp only [TermScope.allOK, Bool.and_eq_true] at hok
      exact ⟨hok.2, hσs, TermScope.envDRF_cons (fun _ => by first | rfl | (cases n <;> rfl))
        (fun y hy hne => he y (TermScope.free_let_body hy hne)), hstk⟩
    · exact h0 j t hj'

/-- **`RunScope` along every solo run** of a checked program. -/
theorem solo_drf {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c1 : Cfg}
    (hp : ProgScopeOK p = true) (h : Solo p k arch i c c1) : RunScope c → RunScope c1 := by
  induction h with
  | refl => exact id
  | thread hs _ ih => exact fun h0 => ih (drf_thread hp h0 hs)
  | prom a v w _ _ ih => exact fun h0 => ih (drf_prom h0)
  | ext hs _ ih => exact fun h0 => ih (drf_ext h0 hs)

/-! ## From the frame-only alternative to the run scope -/

/-- Under `allOK` (no ticket operation), the frame-only alternative is a capability term:
`StepScope ∨ StepScopeR` gives `ScopeD`. -/
theorem scopeD_of {cx : Cx} {σs : List Ty} {t : Expr} (hok : allOK t = true)
    (h : StepScope cx t ∨ StepScopeR σs cx t) : ScopeD σs cx t := by
  rcases h with h | h
  · exact .inl h
  cases t with
  | let_ x op e =>
    simp only [allOK, Bool.and_eq_true] at hok
    cases op
    case borrow a b => exact .inr ⟨h, x, e, .inl ⟨a, b, rfl⟩⟩
    case freeze a => exact .inr ⟨h, x, e, .inr (.inl ⟨a, rfl⟩)⟩
    case endBorrow y => exact .inr ⟨h, x, e, .inr (.inr ⟨y, rfl⟩)⟩
    all_goals exact .inl (by simp_all [StepScopeR, OpScopeR, StepScope, OpScope, opOK])
  | cas => simp [StepScopeR] at h
  | casp => simp [StepScopeR] at h
  | tail => exact .inl (by simpa [StepScopeR, StepScope] using h)
  | _ => exact .inl (by simp [StepScope])

/-- **`ScopeAt` at a `RunScope` configuration** of a checked program. -/
theorem scopeAt_of {p : Prog} {i : Nat} {c : Cfg} (h0 : RunScope c) : ScopeAt p i c := by
  intro th hth hns ρ η cx _ hT _ hi
  have h := h0 i th hth
  exact scopeD_of h.ok (scope_termV hT hi.2.1 h.ok h.env hns)

/-! ## The split run facts -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The scope half of `CertRunC`. -/
def CertScopeC (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAt p i c1

/-- The `NoHoldPub` half of `CertRunC` (named run fact). -/
def CertWinC (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → NoHoldPubA p k arch (Cut Eg i S) (Cut Eg i S) i c1

/-- (D+) **The field form of `CertWinC`**: `NoHoldPubN`, at the unseen publishes only (`certWinC_of_N`). -/
def CertWinCN (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtx p k arch Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → NoHoldPubN p k arch (Cut Eg i S) (Cut Eg i S) i c1

/-- The scope half of `CertRunP`. -/
def CertScopeP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → ScopeAt p j c1

/-- The `NoHoldPub` half of `CertRunP` (named run fact). -/
def CertWinP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → NoHoldPubA p k arch (Cut Eg j S) (Cut Eg j S) j c1) ∧
    (∀ (HP' HS' : Res) (cr' db' : Ts → Res) S1,
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (Tot j) HP' HS' cr' db' S1 →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        NoHoldPubA p k arch (Cut Eg j S1)
          (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S1) j c1)

/-- (D+) **The field form of `CertWinP`**: `NoHoldPubN`, at the unseen publishes only (`certWinP_of_N`). -/
def CertWinPN (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtx p k arch Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → NoHoldPubN p k arch (Cut Eg j S) (Cut Eg j S) j c1) ∧
    (∀ (HP' HS' : Res) (cr' db' : Ts → Res) S1,
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (Tot j) HP' HS' cr' db' S1 →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        NoHoldPubN p k arch (Cut Eg j S1)
          (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S1) j c1)

/-- (spawn) **`CertWinCN` over runs with an extra relation `Sp`**: `TCtx` -> `TCtxX … Sp`. -/
def CertWinCNX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → NoHoldPubN p k arch (Cut Eg i S) (Cut Eg i S) i c1

/-- (spawn) **`CertWinPN` over runs with an extra relation `Sp`**: `PCtx` -> `PCtxX … Sp`. -/
def CertWinPNX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → NoHoldPubN p k arch (Cut Eg j S) (Cut Eg j S) j c1) ∧
    (∀ (HP' HS' : Res) (cr' db' : Ts → Res) S1,
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (Tot j) HP' HS' cr' db' S1 →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        NoHoldPubN p k arch (Cut Eg j S1)
          (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S1) j c1)

/-- **`CertScopeC` holds** for a program passing `ProgScopeOK`, from a `RunScope` start. -/
theorem certScopeC_of (hp : ProgScopeOK p = true) (h0 : TermScope.RunScopeR p k arch Sp c0) : CertScopeC p k arch Sp Init MintOK c0 :=
  fun X _ h1 _ => scopeAt_of (solo_drf hp h1 (run_drf hp h0 X.run))

/-- **`CertScopeP` holds** for a program passing `ProgScopeOK`, from a `RunScope` start. -/
theorem certScopeP_of (hp : ProgScopeOK p = true) (h0 : TermScope.RunScopeR p k arch Sp c0) : CertScopeP p k arch Sp Init MintOK c0 :=
  fun X _ h1 _ => scopeAt_of (solo_drf hp h1 (drf_prom (run_drf hp h0 X.run)))

/-- (D+) The field `CertWinCN` gives `CertWinC` (`TermDPlus.noHoldPubA_of_N` under the binders). -/
theorem certWinC_of_N (h : CertWinCNX p k arch Sp Init MintOK c0) : CertWinC p k arch Sp Init MintOK c0 :=
  fun X S hS c1 h1 h2 => TermDPlus.noHoldPubA_of_N (h X S hS c1 h1 h2)

/-- (D+) The field `CertWinPN` gives `CertWinP`. -/
theorem certWinP_of_N (h : CertWinPNX p k arch Sp Init MintOK c0) : CertWinP p k arch Sp Init MintOK c0 :=
  fun X => ⟨fun S hS c1 h1 h2 => TermDPlus.noHoldPubA_of_N ((h X).1 S hS c1 h1 h2),
    fun HP' HS' cr' db' S1 hS c1 h1 h2 => TermDPlus.noHoldPubA_of_N ((h X).2 HP' HS' cr' db' S1 hS c1 h1 h2)⟩

theorem certRunC_of (hs : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0) :
    TermCohLe.CertRunC p k arch Sp Init MintOK c0 :=
  fun X S hS c1 h1 h2 => ⟨hs X c1 h1 h2, hw X S hS c1 h1 h2⟩

theorem certRunP_of (hs : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0) :
    TermNoHold.CertRunP p k arch Sp Init MintOK c0 :=
  fun X S hS c1 h1 h2 => ⟨hs X c1 h1 h2, (hw X).1 S hS c1 h1 h2⟩

end

end TermCertScope

#print axioms TermCertScope.solo_drf
#print axioms TermCertScope.scopeD_of
#print axioms TermCertScope.scopeAt_of
#print axioms TermCertScope.certScopeC_of
#print axioms TermCertScope.certScopeP_of
#print axioms TermCertScope.certRunC_of
#print axioms TermCertScope.certRunP_of
#print axioms TermCertScope.certWinC_of_N
#print axioms TermCertScope.certWinP_of_N
#print axioms TermCertScope.drf_ext
