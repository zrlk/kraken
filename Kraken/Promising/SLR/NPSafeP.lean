/-
**Prototype.** Can `NPSafe` be generalised in place?

`NPSafeP` is `NPSafe` (`Promising/PromiseSafe.lean`) with its two
policy-carrying conjuncts abstracted:

- the **prepay guard** `G` (today `Thread.RelFulfilsLive`, whose write case
  is the syntactic `A.storeKind k = .rel`), and
- the **K2 frame** `K` (today "for every `ρ`, reach at bounds `≤ c₁.mem.last`
  does not grow", `ReachFrame` in `SLR/Cond3.lean`).

`NPSafeP_G₀_K₀` shows that the instance at the current guard and frame *is*
`NPSafe`, definitionally (`rfl` after unsealing the well-founded
definitions). The scoped frame `K2Scope Kρ` restricts K2 to resources `ρ`
satisfying `Kρ g₁ ρ`; at `Kρ := fun _ _ => True` it is equal to `K2₀` only
propositionally (`True → P` is not `P`), see `K2Scope_true`.

Nothing imports this file.
-/
import Kraken.Promising.SLR.Theorem1
import Kraken.Promising.RelFulfilsLive

namespace Kraken.Promising

variable {I : ISA}

/-- A prepay guard: which promises (of thread `tid`, with the promise
appended to the thread, against the appended memory) the prepay conjunct must
handle. `NPSafe` uses `Thread.RelFulfilsLive`. -/
abbrev PrepayGuard (I : ISA) := Arch → Nat → Time → Thread I → Memory → Prop

/-- A K2 frame: what a step of thread `tid` must preserve about the reach of
resources at bounds `≤ B`, from ghost `g₁` to `g'`. -/
abbrev K2Frame (M : ResModel I) := M.Ghost → M.Ghost → Time → Prop

/-- The current guard. -/
abbrev G₀ : PrepayGuard I := fun A tid ts t mem => t.RelFulfilsLive A tid ts mem

/-- The current K2 frame: over every `ρ`. -/
abbrev K2₀ (M : ResModel I) : K2Frame M :=
  fun g₁ g' B => ∀ b, b ≤ B → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b

/-- K2 restricted to resources in scope (`Kρ g₁ ρ`), e.g. option (S):
resources whose acquire ids were all allocated in `g₁`. -/
abbrev K2Scope (M : ResModel I) (Kρ : M.Ghost → M.R → Prop) : K2Frame M :=
  fun g₁ g' B => ∀ b, b ≤ B → ∀ ρ, Kρ g₁ ρ → ∀ x, M.reach ρ g' x b → M.reach ρ g₁ x b

theorem K2Scope_true (M : ResModel I) : K2Scope M (fun _ _ => True) = K2₀ M := by
  funext g₁ g' B
  simp only [K2Scope, K2₀, forall_const]

section Safety

variable (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat)
  (G : PrepayGuard I) (K : K2Frame M)

/-- `NPSafe` with the prepay guard `G` and the K2 frame `K` abstracted; the
body is otherwise a verbatim copy. -/
def NPSafeP : Nat → Nat → Prop → Config I → M.R → M.Ghost → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, 0, cl, c, r, g => ∀ m, NPSafeP n m cl c r g
  | n + 1, m + 1, cl, c, r, g =>
    ∀ c₁ g₁, EnvExt tid c c₁ → M.ghostLe g g₁ →
    (cl → c₁.Done tid → B c₁ r g₁) ∧
    (∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → NPStepBy A tid c₁ c' →
      c₁.MachInv → c₁.WfProm tid → c'.WfProm tid →
      (∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
        (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
        NPSafeP (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧ M.acqLe r' g' r g₁ ∧
        (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
        K g₁ g' c₁.mem.last ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b)) ∧
    (∀ (rF : Nat → M.R) (t₁ : Thread I) (w : Msg), c₁.threads[tid]? = some t₁ →
      M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → c₁.MachInv →
      (∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      G A tid (c₁.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
        (c₁.mem.append { w with tid }).1 →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafeP (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        K g₁ g' c₁.mem.last ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b))
termination_by n m => (n, m)

end Safety

example (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat) :
    NPSafeP M A B tid G₀ (K2₀ M) = NPSafe M A B tid := by with_unfolding_all rfl

unseal NPSafeP NPSafe in
/-- **Question 1: definitional.** At the current guard and frame, `NPSafeP`
is `NPSafe`: `rfl` once the two well-founded definitions are unsealed (also
`with_unfolding_all rfl`, or `delta NPSafeP NPSafe; rfl`). Without unsealing,
plain `rfl` fails (irreducible well-founded definitions). -/
theorem NPSafeP_G₀_K₀ (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat) :
    NPSafeP M A B tid G₀ (K2₀ M) = NPSafe M A B tid := rfl

example (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat) :
    NPSafeP M A B tid G₀ (K2₀ M) = NPSafe M A B tid := by delta NPSafeP NPSafe; rfl

/-! ## The accessor lemmas, generic in `G` and `K`

Verbatim copies of `NPSafe.envExt`, `.step`, `.prepay`, `.mono_flag`
(`SLR/Theorem1.lean`), `.done`, `.stepAt` (`SLR/Theorem1Proof.lean`) and
`.prepayAt` (`SLR/Theorem1D1.lean`) with `NPSafe` renamed, the guard
hypothesis written `G …` and the K2 conclusion written `K g₁ g' c₁.mem.last`.
No proof line changed. These are the only places in the Theorem 1′ chain
that unfold `NPSafe`, apart from the rule-side inductions `NPSafe.of_inv`
and `NPSafe.of_ruleRX`. -/

section Accessors

variable {A : Arch}

/-- **`NPSafe` is closed under environment extension and ghost growth**
(case (b) of Theorem 1′'s induction: another thread's step, or a promise of
`tid`, leaves `tid`'s `NPSafe` applicable), provided the ghost growth marks
none of `tid`'s promises pending that were not pending before (`hp`: in any
further extension `c₂`, a pending promise of `tid` at `g₁` was pending at
`g`; option (B): only `tid`'s own prepayments mark its promises pending). -/
theorem NPSafeP.envExt {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} (L : M.Laws) {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid : Nat} : ∀ {n m : Nat} {cl : Prop} {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost},
    NPSafeP M A B tid G K n m cl c r g → EnvExt tid c c₁ → M.ghostLe g g₁ →
    (∀ c₂ t₂, EnvExt tid c₁ c₂ → c₂.threads[tid]? = some t₂ → ∀ ts ∈ t₂.prom, M.pendingAt g₁ ts →
      M.pendingAt g ts) →
    NPSafeP M A B tid G K n m cl c₁ r g₁
  | 0, _, _, _, _, _, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, _, _, _, _, _, _, h, he, hg, hp => by
    rw [NPSafeP] at h ⊢
    exact fun m => NPSafeP.envExt L (h m) he hg hp
  | n + 1, m + 1, _, _, _, _, _, _, h, he, hg, hp => by
    rw [NPSafeP] at h ⊢
    intro c₂ g₂ he₂ hg₂
    obtain ⟨hd, hs, hpp⟩ := h c₂ g₂ (he.trans he₂) (L.ghostLe_trans _ _ _ hg hg₂)
    refine ⟨hd, fun rF c' E hst hinv hw hw' hpe => hs rF c' E hst hinv hw hw' fun t ht ts hts h2 =>
      hp c₂ t he₂ ht ts hts (hpe t ht ts hts h2), fun rF t₁ w ht E hinv hpe hrel =>
      hpp rF t₁ w ht E hinv (fun ts hts h2 => hp c₂ t₁ he₂ ht ts hts (hpe ts hts h2)) hrel⟩

/-- **`NPSafe`'s step at the configuration itself** (case (a) of Theorem 1′'s
induction, `c₁ = c`, `g₁ = g`): `EnvExt.refl` and `ghostLe_refl`; the
own-pending hypothesis is trivial at `g₁ = g`. -/
theorem NPSafeP.step {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} (L : M.Laws) {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafeP M A B tid G K (n + 1) (m + 1) cl c r g) :
    (cl → c.Done tid → B c r g) ∧
    ∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g (fun _ => True) c → NPStepBy A tid c c' →
      c.MachInv → c.WfProm tid → c'.WfProm tid →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g g' ∧
        (∀ ts, M.pendingAt g ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g ts) ∧
        NPSafeP M A B tid G K (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g (fun _ => False) c) c' r' g' ∧
        M.acqLe r' g' r g ∧
        (∀ w, Written tid c c' w → M.owns r w.loc) ∧
        K g g' c.mem.last ∧
        (∀ b, b ≤ c.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g x b) := by
  rw [NPSafeP] at h
  obtain ⟨hd, hs, -⟩ := h c g (EnvExt.refl _ _) (L.ghostLe_refl g)
  exact ⟨hd, fun rF c' E hs' hinv hw hw' => hs rF c' E hs' hinv hw hw' fun _ _ _ _ h => h⟩

/-- **`NPSafe`'s prepay conjunct at the configuration itself** (case (d1) of
Theorem 1′'s induction under option (B), `c₁ = c`, `g₁ = g`): the release
event of `tid`'s next instruction, which fulfils the new promise, is
accounted at promise time. -/
theorem NPSafeP.prepay {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} (L : M.Laws) {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafeP M A B tid G K (n + 1) (m + 1) cl c r g) (rF : Nat → M.R) (t₁ : Thread I) (w : Msg) (ht : c.threads[tid]? = some t₁)
    (E : M.erase (M.upd rF tid r) g (fun _ => True) c) (hinv : c.MachInv)
    (hrel : G A tid (c.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
        (c.mem.append { w with tid }).1) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
        (c.withThread tid { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
          (c.mem.append { w with tid }).1) ∧
      M.ghostLe g g' ∧ M.pendingAt g' (c.mem.append { w with tid }).2 ∧
      (∀ ts, M.pendingAt g ts → M.pendingAt g' ts) ∧
      (∀ ts, M.pendingAt g' ts → M.pendingAt g ts ∨ ts = (c.mem.append { w with tid }).2) ∧
      NPSafeP M A B tid G K (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g (fun _ => False) c)
        (c.withThread tid { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
          (c.mem.append { w with tid }).1) r' g' ∧
      M.acqLe r' g' r g ∧
      K g g' c.mem.last ∧
      (∀ b, b ≤ c.mem.last →
        (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, M.reach r' g' x b → M.reach r g x b) := by
  rw [NPSafeP] at h
  exact (h c g (EnvExt.refl _ _) (L.ghostLe_refl g)).2.2 rF t₁ w ht E hinv (fun _ _ h => h) hrel

/-- **The clean flag is antitone**: `NPSafe` with flag `cl` gives
`NPSafe` with any flag `cl'` that implies it. The resource conjuncts do not
mention the flag; the Done conjunct is asked under a stronger hypothesis, and
continuations' flags `cl' ∧ V` imply `cl ∧ V`. In particular a proof of
`NPSafe … True …` gives every flag, and a proof that never uses validity can
be stated for every `cl`. -/
theorem NPSafeP.mono_flag {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid : Nat} : ∀ {n m : Nat} {cl cl' : Prop} {c : Config I} {r : M.R} {g : M.Ghost},
    (cl' → cl) → NPSafeP M A B tid G K n m cl c r g → NPSafeP M A B tid G K n m cl' c r g
  | 0, _, _, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, _, _, _, _, _, hc, h => by
    rw [NPSafeP] at h ⊢
    exact fun m => NPSafeP.mono_flag hc (h m)
  | n + 1, m + 1, _, _, _, _, _, hc, h => by
    rw [NPSafeP] at h ⊢
    intro c₁ g₁ he hg
    obtain ⟨hd, hs, hpp⟩ := h c₁ g₁ he hg
    refine ⟨fun h' => hd (hc h'), fun rF c' E hst hinv hw hw' hpe => ?_,
      fun rF t₁ w ht E hinv hpe hrel => ?_⟩
    · obtain ⟨r', g', E', hg', hk, hk', hn, rest⟩ := hs rF c' E hst hinv hw hw' hpe
      exact ⟨r', g', E', hg', hk, hk', NPSafeP.mono_flag (fun h' => ⟨hc h'.1, h'.2⟩) hn, rest⟩
    · obtain ⟨r', g', E', hg', hp', hk, hk', hn, rest⟩ := hpp rF t₁ w ht E hinv hpe hrel
      exact ⟨r', g', E', hg', hp', hk, hk', NPSafeP.mono_flag (fun h' => ⟨hc h'.1, h'.2⟩) hn, rest⟩

/-- `NPSafe`'s Done conjunct at an environment extension, from a token with
at least two step indices. -/
theorem NPSafeP.done {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafeP M A B tid G K (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁) (hcl : cl) (hd : c₁.Done tid) : B c₁ r g₁ := by
  rw [NPSafeP] at h
  have h1 := h (0 + 1)
  rw [NPSafeP] at h1
  exact (h1 c₁ g₁ he hg).1 hcl hd

/-- `NPSafe`'s step at an environment extension, from a token with at least
two step indices: the continuation keeps one. -/
theorem NPSafeP.stepAt {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafeP M A B tid G K (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁)
    (hown : ∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts)
    (rF : Nat → M.R) (c' : Config I) (E : M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁)
    (hs : NPStepBy A tid c₁ c') (hinv : c₁.MachInv) (hw : c₁.WfProm tid) (hw' : c'.WfProm tid) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
      (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
        M.pendingAt g' ts) ∧
      (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
      NPSafeP M A B tid G K (k + 1) 0 (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧
      M.acqLe r' g' r g₁ ∧
      (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
      K g₁ g' c₁.mem.last ∧
      (∀ b, b ≤ c₁.mem.last →
        (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
        ∀ x, M.reach r' g' x b → M.reach r g₁ x b) := by
  rw [NPSafeP] at h
  have h1 := h (0 + 1)
  rw [NPSafeP] at h1
  exact (h1 c₁ g₁ he hg).2.1 rF c' E hs hinv hw hw' hown

/-- `NPSafe`'s prepay conjunct at an environment extension, from a token with
at least two step indices: the continuation keeps one. -/
theorem NPSafeP.prepayAt {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafeP M A B tid G K (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁)
    (rF : Nat → M.R) (t₁ : Thread I) (w : Msg) (ht : c₁.threads[tid]? = some t₁)
    (E : M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁) (hinv : c₁.MachInv)
    (hown : ∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts)
    (hrel : G A tid (c₁.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
        (c₁.mem.append { w with tid }).1) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafeP M A B tid G K (k + 1) 0 (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        K g₁ g' c₁.mem.last ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b) := by
  rw [NPSafeP] at h
  have h1 := h (0 + 1)
  rw [NPSafeP] at h1
  exact (h1 c₁ g₁ he hg).2.2 rF t₁ w ht E hinv hown hrel

/-- **`NPSafeP` is antitone in the guard and monotone in the frame**: a
stronger guard asks for fewer prepayments, a weaker frame asks less of each
step. Same induction as `NPSafe.mono_flag`. -/
theorem NPSafeP.mono {M : ResModel I} {B : Config I → M.R → M.Ghost → Prop} {tid : Nat}
    {G G' : PrepayGuard I} {K K' : K2Frame M}
    (hG : ∀ A tid ts t mem, G' A tid ts t mem → G A tid ts t mem) (hK : ∀ g₁ g' b, K g₁ g' b → K' g₁ g' b) :
    ∀ {n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost},
    NPSafeP M A B tid G K n m cl c r g → NPSafeP M A B tid G' K' n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, _, _, _, _, h => by
    rw [NPSafeP] at h ⊢
    exact fun m => NPSafeP.mono hG hK (h m)
  | n + 1, m + 1, _, _, _, _, h => by
    rw [NPSafeP] at h ⊢
    intro c₁ g₁ he hg
    obtain ⟨hd, hs, hpp⟩ := h c₁ g₁ he hg
    refine ⟨hd, fun rF c' E hst hinv hw hw' hpe => ?_, fun rF t₁ w ht E hinv hpe hrel => ?_⟩
    · obtain ⟨r', g', E', hg', hk, hk', hn, hacq, hown, hK2, hK1⟩ := hs rF c' E hst hinv hw hw' hpe
      exact ⟨r', g', E', hg', hk, hk', NPSafeP.mono hG hK hn, hacq, hown, hK _ _ _ hK2, hK1⟩
    · obtain ⟨r', g', E', hg', hp', hk, hk', hn, hacq, hK2, hK1⟩ := hpp rF t₁ w ht E hinv hpe (hG _ _ _ _ _ hrel)
      exact ⟨r', g', E', hg', hp', hk, hk', NPSafeP.mono hG hK hn, hacq, hK _ _ _ hK2, hK1⟩

/-- Every existing `NPSafe` proof (e.g. `NPSafe.of_ruleRX`) is an `NPSafeP`
proof for any guard below `G₀` and any frame above `K2₀`; in particular for
option (S)'s `K2Scope`. -/
theorem NPSafe.toP {M : ResModel I} {B : Config I → M.R → M.Ghost → Prop} {tid : Nat}
    {G' : PrepayGuard I} {K' : K2Frame M}
    (hG : ∀ A tid ts t mem, G' A tid ts t mem → G₀ A tid ts t mem) (hK : ∀ g₁ g' b, K2₀ M g₁ g' b → K' g₁ g' b)
    {n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafe M A B tid n m cl c r g) : NPSafeP M A B tid G' K' n m cl c r g :=
  NPSafeP.mono hG hK (by rw [NPSafeP_G₀_K₀]; exact h)

/-- Option (S)'s frame is implied by the current one. -/
theorem K2₀.toScope {M : ResModel I} (Kρ : M.Ghost → M.R → Prop) {g₁ g' : M.Ghost} {b : Time}
    (h : K2₀ M g₁ g' b) : K2Scope M Kρ g₁ g' b :=
  fun b' hb ρ _ x hr => h b' hb ρ x hr

end Accessors

/-! ## The axioms the Theorem 1′ chain uses (question 3) -/

/-- **What Theorem 1′ uses of the prepay guard.** The chain (`Theorem1Proof`,
`Theorem1D1`) uses the fulfilling instruction only through
- `relPre_lt`: the thread is release-bounded below the promise ((S2)
  `stutterStep_path`, (S1′) `advance_path`, case (d2), the replay of (d1));
- `restrict`: the guard replays on a memory prefix ((S1′):
  the advanced thread restricted to the memory at the promise step; (d1):
  the prepay hypothesis at the virtual configuration).
`Status` and `Config.VirtualOf` record the weak form `Thread.RelFulfils`;
a generic chain records `G` itself, so nothing else is needed. -/
structure GuardOK (G : PrepayGuard I) : Prop where
  relPre_lt : ∀ {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory},
    G A tid ts t mem → t.views.FwdOk → t.views.relPre < ts
  restrict : ∀ {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {M M' : Memory},
    M.Prefix M' → ts ≤ M.last → t.views.FwdOk → G A tid ts t M' →
    t.views.vwOldNT ≤ M.last → t.NextNoNT A → G A tid ts (t.restrict M) M

/-- The current guard satisfies `GuardOK`. -/
theorem guardOK_G₀ : GuardOK (I := I) G₀ where
  relPre_lt h hf := h.toRelFulfils.relPre_lt hf
  restrict hM hts hf h hnt hnx := Thread.RelFulfilsLive.restrict hM hts hf h hnt hnx

/-- The weak guard `Thread.RelFulfils` (no "no promise left dead" side
condition). The existing Theorem 1′ chain records it in `Status` and
`Config.VirtualOf` (the *virtual* guard), while `NPSafe`, `RelFulfilled` and
`PromisePure` use `G₀` (the *prepay* guard). The generic chain takes the two
guards separately, so that the existing chain is its instance at `G₀`, `GRF`,
`K2₀`. -/
abbrev GRF : PrepayGuard I := fun A tid ts t mem => t.RelFulfils A tid ts mem

/-- `Thread.RelFulfils` satisfies `GuardOK`. -/
theorem guardOK_GRF : GuardOK (I := I) GRF where
  relPre_lt h hf := Thread.RelFulfils.relPre_lt h hf
  restrict hM hts hf h hnt hnx := Thread.RelFulfils.restrict hM hts hf h hnt hnx

/-- The prepay guard `G₀` is below the virtual guard `GRF`. -/
theorem G₀_le_GRF {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : G₀ A tid ts t mem) : GRF A tid ts t mem :=
  Thread.RelFulfilsLive.toRelFulfils h

/-- **What condition (3) uses of K2** (`MicroStep.pull`, `SLR/Cond3Proof.lean`,
its only consumer): across a step of thread `s` with frame `K g g' B`, the
bounded reach of *another existing* thread `i` (its resource unchanged) at
bounds `≤ B` does not grow, at a configuration that is erased
(`AnnRun.erase`). Only resources `rF i` of threads `i < c.threads.size` of
an erased configuration are ever fed to K2. -/
def K2OK (M : ResModel I) (K : K2Frame M) : Prop :=
  ∀ (rF : Nat → M.R) (g g' : M.Ghost) (T : Nat → Prop) (c : Config I) (i : Nat) (B : Time),
    M.erase rF g T c → i < c.threads.size → K g g' B →
    ∀ b, b ≤ B → ∀ x, M.reach (rF i) g' x b → M.reach (rF i) g x b

/-- The current frame satisfies `K2OK` (it does not need erasure). -/
theorem k2OK_K2₀ (M : ResModel I) : K2OK M (K2₀ M) :=
  fun rF _ _ _ _ i _ _ _ hK b hb x h => hK b hb (rF i) x h

/-! ## The step guard

the failing-RMW route (`SLR/EnvG/RmwFailRule.lean`): a release RMW that fails while the
thread's prepaid promise is pending cannot satisfy `NPSafeP`'s step conjunct,
which asks for *every* live outcome. The Theorem 1′ chain only asks that
conjunct for steps after which every promise of the thread that was pending
is gone (`StepFulP`): see `caseNow'` (`SLR/Theorem1Proof.lean`) and the
replay of `caseD1'` (`SLR/Theorem1D1.lean`), its only two `stepAt` sites.

`NPSafePS … S` is `NPSafeP` whose step conjunct is wrapped in a *step guard*
`S` (a modality on the conjunct's conclusion). The chain is generic in `S`
and discharges it at the two sites from `StepFulP` (`StepGuard.elim`).

- `StepGuard.top`: the identity; `NPSafePS … (StepGuard.top M)` *is*
  `NPSafeP` (`NPSafePS_top`, `rfl` after unsealing), so the existing chain is
  the instance at `top`, definitionally.
- `StepGuard.ofProp S hS`: the guard "assume `S tid c₁ g₁ c'`" for a `Prop`
  guard `S` implied by `StepFulP`; `StepGuard.ful` is the one at `StepFulP`
  (the failing-RMW route's `NPSafeF` is `NPSafePS … G₀ (K2₀ _) (StepGuard.ful _)`).

A guard is a modality rather than a bare `Prop` so that `top` is the
identity on the nose (`True → P` is not `P` definitionally). -/

/-- **The fulfilling step condition**: every promise of `tid` pending at `g₁`
before the step is no longer a promise of `tid` after it. Same body as
the failing-RMW route's `EnvG.StepFul`. -/
def StepFulP (M : ResModel I) (tid : Nat) (c₁ : Config I) (g₁ : M.Ghost) (c' : Config I) : Prop :=
  ∀ t t', c₁.threads[tid]? = some t → c'.threads[tid]? = some t' → ∀ ts ∈ t.prom, M.pendingAt g₁ ts →
    ts ∉ t'.prom

/-- **A step guard** for `NPSafePS`: a modality `guard tid c₁ g₁ c'` on the
conclusion of the step conjunct (thread `tid`, from `c₁` at ghost `g₁` to
`c'`). It is monotone, every proposition implies its guarded form (`intro`:
an unguarded token is a guarded one, `NPSafeP.toS`), and it can be
eliminated at a fulfilling step (`elim`: what the Theorem 1′ chain uses). -/
structure StepGuard (M : ResModel I) where
  guard : Nat → Config I → M.Ghost → Config I → Prop → Prop
  mono : ∀ {tid : Nat} {c₁ : Config I} {g₁ : M.Ghost} {c' : Config I} {P Q : Prop},
    (P → Q) → guard tid c₁ g₁ c' P → guard tid c₁ g₁ c' Q
  intro : ∀ {tid : Nat} {c₁ : Config I} {g₁ : M.Ghost} {c' : Config I} {P : Prop},
    P → guard tid c₁ g₁ c' P
  elim : ∀ {tid : Nat} {c₁ : Config I} {g₁ : M.Ghost} {c' : Config I} {P : Prop},
    StepFulP M tid c₁ g₁ c' → guard tid c₁ g₁ c' P → P

/-- The trivial step guard (`S := ⊤`): the identity modality. -/
abbrev StepGuard.top (M : ResModel I) : StepGuard M where
  guard _ _ _ _ P := P
  mono h := h
  intro h := h
  elim _ h := h

/-- The step guard "assume `S tid c₁ g₁ c'`", for a `Prop` guard `S` implied
by the fulfilling step condition. -/
abbrev StepGuard.ofProp (M : ResModel I) (S : Nat → Config I → M.Ghost → Config I → Prop)
    (hS : ∀ {tid : Nat} {c₁ : Config I} {g₁ : M.Ghost} {c' : Config I}, StepFulP M tid c₁ g₁ c' → S tid c₁ g₁ c') :
    StepGuard M where
  guard tid c₁ g₁ c' P := S tid c₁ g₁ c' → P
  mono h hp hs := h (hp hs)
  intro h _ := h
  elim hf h := h (hS hf)

/-- The fulfilling step guard (`S := StepFul`): the step conjunct
is asked only for steps that fulfil every pending promise of the thread. -/
abbrev StepGuard.ful (M : ResModel I) : StepGuard M := StepGuard.ofProp M (StepFulP M) id

section SafetyS

variable (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat)
  (G : PrepayGuard I) (K : K2Frame M) (S : StepGuard M)

/-- **`NPSafeP` with a step guard** `S`: the step conjunct's conclusion is
`S.guard tid c₁ g₁ c' (…)`; the body is otherwise a verbatim copy of
`NPSafeP`. At `S := StepGuard.top M` it is `NPSafeP` (`NPSafePS_top`). -/
def NPSafePS : Nat → Nat → Prop → Config I → M.R → M.Ghost → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, 0, cl, c, r, g => ∀ m, NPSafePS n m cl c r g
  | n + 1, m + 1, cl, c, r, g =>
    ∀ c₁ g₁, EnvExt tid c c₁ → M.ghostLe g g₁ →
    (cl → c₁.Done tid → B c₁ r g₁) ∧
    (∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → NPStepBy A tid c₁ c' →
      c₁.MachInv → c₁.WfProm tid → c'.WfProm tid →
      (∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      S.guard tid c₁ g₁ c'
      (∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
        (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
        NPSafePS (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧ M.acqLe r' g' r g₁ ∧
        (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
        K g₁ g' c₁.mem.last ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b))) ∧
    (∀ (rF : Nat → M.R) (t₁ : Thread I) (w : Msg), c₁.threads[tid]? = some t₁ →
      M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → c₁.MachInv →
      (∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      G A tid (c₁.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
        (c₁.mem.append { w with tid }).1 →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafePS (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        K g₁ g' c₁.mem.last ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b))
termination_by n m => (n, m)

/-- `NPSafePS` at the fulfilling step guard (the failing-RMW route's `NPSafeF`, generic in
`G` and `K`). -/
abbrev NPSafePF : Nat → Nat → Prop → Config I → M.R → M.Ghost → Prop :=
  NPSafePS M A B tid G K (StepGuard.ful M)

end SafetyS

unseal NPSafePS NPSafeP in
/-- **At the trivial step guard, `NPSafePS` is `NPSafeP`**, definitionally
(`rfl` once the two well-founded definitions are unsealed). So every
statement of the chain at `S := StepGuard.top _` is the existing statement. -/
theorem NPSafePS_top (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat)
    (G : PrepayGuard I) (K : K2Frame M) :
    NPSafePS M A B tid G K (StepGuard.top M) = NPSafeP M A B tid G K := rfl

section AccessorsS

variable {A : Arch}

/-- `NPSafeP.step` for `NPSafePS`: the step conjunct comes guarded. -/
theorem NPSafePS.step {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S : StepGuard M} (L : M.Laws)
    {B : Config I → M.R → M.Ghost → Prop}
    {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafePS M A B tid G K S (n + 1) (m + 1) cl c r g) :
    (cl → c.Done tid → B c r g) ∧
    ∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g (fun _ => True) c → NPStepBy A tid c c' →
      c.MachInv → c.WfProm tid → c'.WfProm tid →
      S.guard tid c g c'
      (∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g g' ∧
        (∀ ts, M.pendingAt g ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g ts) ∧
        NPSafePS M A B tid G K S (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g (fun _ => False) c) c' r' g' ∧
        M.acqLe r' g' r g ∧
        (∀ w, Written tid c c' w → M.owns r w.loc) ∧
        K g g' c.mem.last ∧
        (∀ b, b ≤ c.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g x b)) := by
  rw [NPSafePS] at h
  obtain ⟨hd, hs, -⟩ := h c g (EnvExt.refl _ _) (L.ghostLe_refl g)
  exact ⟨hd, fun rF c' E hs' hinv hw hw' => hs rF c' E hs' hinv hw hw' fun _ _ _ _ h => h⟩

/-- **The clean flag is antitone** (`NPSafeP.mono_flag`), for `NPSafePS`. -/
theorem NPSafePS.mono_flag {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S : StepGuard M} {A : Arch}
    {B : Config I → M.R → M.Ghost → Prop}
    {tid : Nat} : ∀ {n m : Nat} {cl cl' : Prop} {c : Config I} {r : M.R} {g : M.Ghost},
    (cl' → cl) → NPSafePS M A B tid G K S n m cl c r g → NPSafePS M A B tid G K S n m cl' c r g
  | 0, _, _, _, _, _, _, _, _ => by simp [NPSafePS]
  | n + 1, 0, _, _, _, _, _, hc, h => by
    rw [NPSafePS] at h ⊢
    exact fun m => NPSafePS.mono_flag hc (h m)
  | n + 1, m + 1, _, _, _, _, _, hc, h => by
    rw [NPSafePS] at h ⊢
    intro c₁ g₁ he hg
    obtain ⟨hd, hs, hpp⟩ := h c₁ g₁ he hg
    refine ⟨fun h' => hd (hc h'), fun rF c' E hst hinv hw hw' hpe => ?_,
      fun rF t₁ w ht E hinv hpe hrel => ?_⟩
    · refine S.mono (fun hx => ?_) (hs rF c' E hst hinv hw hw' hpe)
      obtain ⟨r', g', E', hg', hk, hk', hn, rest⟩ := hx
      exact ⟨r', g', E', hg', hk, hk', NPSafePS.mono_flag (fun h' => ⟨hc h'.1, h'.2⟩) hn, rest⟩
    · obtain ⟨r', g', E', hg', hp', hk, hk', hn, rest⟩ := hpp rF t₁ w ht E hinv hpe hrel
      exact ⟨r', g', E', hg', hp', hk, hk', NPSafePS.mono_flag (fun h' => ⟨hc h'.1, h'.2⟩) hn, rest⟩

/-- `NPSafeP.done` for `NPSafePS`. -/
theorem NPSafePS.done {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S : StepGuard M}
    {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafePS M A B tid G K S (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁) (hcl : cl) (hd : c₁.Done tid) : B c₁ r g₁ := by
  rw [NPSafePS] at h
  have h1 := h (0 + 1)
  rw [NPSafePS] at h1
  exact (h1 c₁ g₁ he hg).1 hcl hd

/-- **`NPSafePS`'s step at an environment extension, at a fulfilling step**
(`NPSafeP.stepAt` with the extra hypothesis `hful`, which eliminates the
step guard). -/
theorem NPSafePS.stepAt {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S : StepGuard M}
    {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafePS M A B tid G K S (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁)
    (hown : ∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts)
    (rF : Nat → M.R) (c' : Config I) (E : M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁)
    (hs : NPStepBy A tid c₁ c') (hinv : c₁.MachInv) (hw : c₁.WfProm tid) (hw' : c'.WfProm tid)
    (hful : StepFulP M tid c₁ g₁ c') :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
      (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
        M.pendingAt g' ts) ∧
      (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
      NPSafePS M A B tid G K S (k + 1) 0 (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧
      M.acqLe r' g' r g₁ ∧
      (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
      K g₁ g' c₁.mem.last ∧
      (∀ b, b ≤ c₁.mem.last →
        (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
        ∀ x, M.reach r' g' x b → M.reach r g₁ x b) := by
  rw [NPSafePS] at h
  have h1 := h (0 + 1)
  rw [NPSafePS] at h1
  exact S.elim hful ((h1 c₁ g₁ he hg).2.1 rF c' E hs hinv hw hw' hown)

/-- `NPSafeP.prepayAt` for `NPSafePS` (the prepay conjunct is unguarded). -/
theorem NPSafePS.prepayAt {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S : StepGuard M}
    {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafePS M A B tid G K S (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁)
    (rF : Nat → M.R) (t₁ : Thread I) (w : Msg) (ht : c₁.threads[tid]? = some t₁)
    (E : M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁) (hinv : c₁.MachInv)
    (hown : ∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts)
    (hrel : G A tid (c₁.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
        (c₁.mem.append { w with tid }).1) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafePS M A B tid G K S (k + 1) 0 (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        K g₁ g' c₁.mem.last ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b) := by
  rw [NPSafePS] at h
  have h1 := h (0 + 1)
  rw [NPSafePS] at h1
  exact (h1 c₁ g₁ he hg).2.2 rF t₁ w ht E hinv hown hrel

/-- **Change the step guard**: a token at `S` is a token at any `S'` whose
guarded form follows from `S`'s. -/
theorem NPSafePS.mapGuard {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S S' : StepGuard M}
    {B : Config I → M.R → M.Ghost → Prop} {tid : Nat}
    (hS : ∀ {c₁ : Config I} {g₁ : M.Ghost} {c' : Config I} {P : Prop}, S.guard tid c₁ g₁ c' P → S'.guard tid c₁ g₁ c' P) :
    ∀ {n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost},
    NPSafePS M A B tid G K S n m cl c r g → NPSafePS M A B tid G K S' n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafePS]
  | n + 1, 0, _, _, _, _, h => by
    rw [NPSafePS] at h ⊢
    exact fun m => NPSafePS.mapGuard hS (h m)
  | n + 1, m + 1, _, _, _, _, h => by
    rw [NPSafePS] at h ⊢
    intro c₁ g₁ he hg
    obtain ⟨hd, hs, hpp⟩ := h c₁ g₁ he hg
    refine ⟨hd, fun rF c' E hst hinv hw hw' hpe => ?_, fun rF t₁ w ht E hinv hpe hrel => ?_⟩
    · refine hS (S.mono (fun hx => ?_) (hs rF c' E hst hinv hw hw' hpe))
      obtain ⟨r', g', E', hg', hk, hk', hn, rest⟩ := hx
      exact ⟨r', g', E', hg', hk, hk', NPSafePS.mapGuard hS hn, rest⟩
    · obtain ⟨r', g', E', hg', hp', hk, hk', hn, rest⟩ := hpp rF t₁ w ht E hinv hpe hrel
      exact ⟨r', g', E', hg', hp', hk, hk', NPSafePS.mapGuard hS hn, rest⟩

/-- **Every `NPSafeP` token is an `NPSafePS` token, at every step guard**
(`StepGuard.intro`; via `NPSafePS_top`). -/
theorem NPSafeP.toS {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} (S : StepGuard M)
    {B : Config I → M.R → M.Ghost → Prop} {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafeP M A B tid G K n m cl c r g) : NPSafePS M A B tid G K S n m cl c r g :=
  NPSafePS.mapGuard (S := StepGuard.top M) (fun h => S.intro h) (by rw [NPSafePS_top]; exact h)

/-- **Every `NPSafePS` token is an `NPSafePF` token** (`StepGuard.elim`): the
fulfilling guard is the weakest the chain can discharge. -/
theorem NPSafePS.toF {M : ResModel I} {G : PrepayGuard I} {K : K2Frame M} {S : StepGuard M}
    {B : Config I → M.R → M.Ghost → Prop} {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafePS M A B tid G K S n m cl c r g) : NPSafePF M A B tid G K n m cl c r g :=
  NPSafePS.mapGuard (fun h hf => S.elim hf h) h

end AccessorsS

#print axioms NPSafeP_G₀_K₀
#print axioms NPSafePS_top
#print axioms NPSafeP.toS
#print axioms NPSafePS.stepAt
#print axioms NPSafe.toP
#print axioms NPSafeP.prepayAt
end Kraken.Promising
