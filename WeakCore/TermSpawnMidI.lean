import WeakCore.TermCkC
import WeakCore.TermSound
import WeakCore.TermSpawnKidI
/-! # TermSpawnMidI — wrap facts for the argument type of a thread started by `spawnI`. -/
open CoreLang CoreTerm CoreTyping TermScope

namespace TermSpawnI

theorem rw_shiftIN (σ : Ty) (env : List Bool) :
    ∀ d, rcarE env (shiftIN d σ) = rcarE env σ ∧ wrapOKE env (shiftIN d σ) = wrapOKE env σ
  | 0 => ⟨rfl, rfl⟩
  | d + 1 => by
      obtain ⟨h1, h2⟩ := rw_shiftIN σ env d
      obtain ⟨g1, g2⟩ := TermA4.rw_shiftI (shiftIN d σ) 0 env
      simp only [shiftIN]; exact ⟨g1.trans h1, g2.trans h2⟩

theorem getD_ge_false {env : List Bool} {k : Nat} (h : env.length ≤ k) : env.getD k false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Substituting closed key-free `wrapOK` arguments is invisible to `rcarE`/`wrapOKE`. -/
theorem rw_substTs (σs : List Ty) (hσ : ∀ σ ∈ σs, TermClose.tb 0 σ = true ∧ argOK σ = true) :
    ∀ (t : Ty) (c d : Nat) (env : List Bool), env.length = c →
      rcarE env (substTs σs c d t) = rcarE env t ∧ wrapOKE env (substTs σs c d t) = wrapOKE env t := by
  intro t
  induction t with
  | tvar k =>
      intro c d env hl
      by_cases hk : k < c
      · simp [substTs, hk]
      · cases hs : σs[k - c]? with
        | none =>
            have hlen : σs.length ≤ k - c := by
              rcases Nat.lt_or_ge (k - c) σs.length with h | h
              · rw [List.getElem?_eq_getElem h] at hs; cases hs
              · exact h
            simp only [substTs, hk, ite_false, hs, rcarE, wrapOKE]
            rw [getD_ge_false (k := k - σs.length) (by omega), getD_ge_false (k := k) (by omega)]
            exact ⟨rfl, trivial⟩
        | some σ =>
            have hm : σ ∈ σs := List.mem_of_getElem? hs
            obtain ⟨htb, hao⟩ := hσ σ hm
            simp only [argOK, Bool.and_eq_true, Bool.not_eq_true'] at hao
            simp only [substTs, hk, ite_false, hs, rcarE, wrapOKE]
            rw [TermSound.shiftTN_tb0 σ htb, (rw_shiftIN σ env d).1, (rw_shiftIN σ env d).2,
              TermA4.rcarE_closed htb, TermA4.wrapOKE_closed htb, getD_ge_false (by omega)]
            exact ⟨hao.2, hao.1⟩
  | prod a b iha ihb =>
      intro c d env hl; obtain ⟨a1, a2⟩ := iha c d env hl; obtain ⟨b1, b2⟩ := ihb c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, a1, a2, b1, b2]
  | sum a b iha ihb =>
      intro c d env hl; obtain ⟨a1, a2⟩ := iha c d env hl; obtain ⟨b1, b2⟩ := ihb c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, a1, a2, b1, b2]
  | code a b _ iha ihb =>
      intro c d env hl; obtain ⟨-, a2⟩ := iha c d env hl; obtain ⟨-, b2⟩ := ihb c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, a2, b2]
  | array i t ih =>
      intro c d env hl; obtain ⟨-, h2⟩ := ih c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h2]
  | ptr μ t ih =>
      intro c d env hl; obtain ⟨-, h2⟩ := ih c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h2]
  | ptrOpt μ t ih =>
      intro c d env hl; obtain ⟨-, h2⟩ := ih c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h2]
  | loc μ t ih =>
      intro c d env hl; obtain ⟨-, h2⟩ := ih c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h2]
  | iall t ih =>
      intro c d env hl; obtain ⟨h1, h2⟩ := ih c (d + 1) env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h1, h2]
  | iex t ih =>
      intro c d env hl; obtain ⟨h1, h2⟩ := ih c (d + 1) env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h1, h2]
  | refine t ψ ih =>
      intro c d env hl; obtain ⟨h1, h2⟩ := ih c d env hl
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h1, h2]
  | tex κ t ih =>
      intro c d env hl; obtain ⟨h1, h2⟩ := ih (c + 1) d (false :: env) (by simp [hl])
      refine ⟨?_, ?_⟩ <;> simp only [substTs, rcarE, wrapOKE, h1, h2]
  | mu t ih =>
      intro c d env hl
      have h0 := (ih (c + 1) d (false :: env) (by simp [hl])).1
      simp only [substTs, rcarE, wrapOKE, h0]
      exact ih (c + 1) d _ (by simp [hl])
  | _ => intro c d env _; exact ⟨rfl, rfl⟩

theorem wrapOK_substTs {σs : List Ty} {t : Ty} (hσ : σs.all (TermClose.tb 0) = true)
    (hσa : σs.all argOK = true) (ht : wrapOK t = true) : wrapOK (substTs σs 0 0 t) = true := by
  unfold wrapOK
  rw [(rw_substTs σs (fun σ hm => ⟨List.all_eq_true.1 hσ σ hm, List.all_eq_true.1 hσa σ hm⟩) t 0 0 [] rfl).2]
  exact ht

end TermSpawnI
#print axioms TermSpawnI.wrapOK_substTs
