import WeakCore.MergeP
import WeakCore.Merge
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! The f-form merge (design decision D1 (a)): copies (`cp`) map to their originals by `f`; every other label
moves by the involution `σ` (`f = σ` off the copies).  Resources pull back along `σ` on `own` keys. -/

def keySw (σ : WeakMem.AllocLabel → WeakMem.AllocLabel) : Key → Key
  | .own l => .own (σ l)
  | k => k

def Res.sw (σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (X : Res) : Res := fun k => X (keySw σ k)

theorem keySw_inv {σ : WeakMem.AllocLabel → WeakMem.AllocLabel} (hs : ∀ m, σ (σ m) = m) (k : Key) :
    keySw σ (keySw σ k) = k := by
  cases k <;> simp [keySw, hs]

theorem Res.sw_zero (σ : WeakMem.AllocLabel → WeakMem.AllocLabel) : Res.sw σ .zero = .zero := rfl

theorem Res.sw_add (σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (X Y : Res) :
    Res.sw σ (X + Y) = Res.sw σ X + Res.sw σ Y := rfl

theorem Res.sw_one {σ : WeakMem.AllocLabel → WeakMem.AllocLabel} (hs : ∀ m, σ (σ m) = m) (k : Key) :
    Res.sw σ (.one k) = .one (keySw σ k) := by
  funext k'
  simp only [Res.sw, Res.one_apply]
  by_cases h : k' = keySw σ k
  · subst h; simp [keySw_inv hs]
  · have : keySw σ k' ≠ k := fun e => h (by rw [← e, keySw_inv hs])
    simp [h, this]

/-- Bijective form of `Res.sw_one` (`τ` is `σ`'s inverse). -/
theorem Res.sw_oneP {σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} (h1 : ∀ m, τ (σ m) = m)
    (h2 : ∀ m, σ (τ m) = m) (k : Key) : Res.sw σ (.one k) = .one (keySw τ k) := by
  funext k'
  simp only [Res.sw, Res.one_apply]
  have e : ∀ k'', keySw σ k'' = k ↔ k'' = keySw τ k := by
    intro k''; cases k <;> cases k'' <;> simp [keySw] <;> first
      | (constructor <;> intro h <;> subst h <;> simp [h1, h2]) | skip
  by_cases h : k' = keySw τ k
  · rw [if_pos ((e k').2 h), if_pos h]
  · rw [if_neg (fun h' => h ((e k').1 h')), if_neg h]

theorem Res.sw_comp {σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} (h1 : ∀ m, τ (σ m) = m) (X : Res) :
    Res.sw σ (Res.sw τ X) = X := by
  funext k; cases k <;> simp [Res.sw, keySw, h1]

theorem Res.sw_rg {σ : WeakMem.AllocLabel → WeakMem.AllocLabel} (hs : ∀ m, σ (σ m) = m) (n : Nat) :
    Res.sw σ (.one (.rg n)) = .one (.rg n) := by rw [Res.sw_one hs]; rfl

structure MergeOKQ (cp : WeakMem.AllocLabel → Prop) (f σ : WeakMem.AllocLabel → WeakMem.AllocLabel)
    (η₁ η₂ : TEnv) : Prop where
  wit : η₁.wit = η₂.wit
  prog : η₁.prog = η₂.prog
  tid : η₁.tid = η₂.tid
  -- (G-c) guards widened to cell labels: box variants (no cell, `f (bv x k) = x`) are exempt.
  fσ : ∀ m, ¬ (cp m ∨ η₁.sto m = none) → σ (f m) = m
  σf : ∀ m, ¬ (cp (σ m) ∨ η₁.sto (σ m) = none) → f (σ m) = m
  sto : ∀ m c, ¬ cp m → η₁.sto m = some c → η₂.sto (f m) = some c
  ini : ∀ m, ¬ cp m → η₁.ini m ≤ η₂.ini (f m)
  rini : ∀ m, ¬ cp m → η₁.rini m ≤ η₂.rini (f m)
  pfr : ∀ m q, ¬ cp m → η₁.pfr m = some q → η₂.pfr (f m) = some q
  seen : ∀ m, ¬ cp m → η₁.seen m → η₂.seen (f m)
  box : ∀ m B, η₁.box m = some B → η₂.box (f m) = some { B with pay := B.pay.map (rl f) }
  cl : ∀ m c', cp m → η₁.sto m = some c' → ∃ c, η₂.sto (f m) = some c ∧ c'.ty = c.ty ∧
    c'.owner = none ∧ c.owner = some η₂.tid
  inil : ∀ m, cp m → η₁.ini m ≤ η₂.rc (f m)
  rinil : ∀ m, cp m → η₁.rini m ≤ η₂.rc (f m)
  pfrl : ∀ m, cp m → ∃ q, η₂.pfr (f m) = some q
  pfrc : ∀ m, cp m → ∃ q, η₁.pfr m = some q ∧ ∀ v : WeakMem.Ts, q ≤ v

section
variable {cp : WeakMem.AllocLabel → Prop} {f σ : WeakMem.AllocLabel → WeakMem.AllocLabel}

theorem MergeOKQ.unsee {η₁ η₂ : TEnv} (h : MergeOKQ cp f σ η₁ η₂) : MergeOKQ cp f σ η₁.unsee η₂.unsee :=
  { wit := h.wit, prog := h.prog, tid := h.tid, fσ := h.fσ, σf := h.σf, sto := h.sto, ini := h.ini,
    rini := h.rini, pfr := h.pfr, seen := fun _ _ e => e.elim, box := h.box, cl := h.cl, inil := h.inil,
    rinil := h.rinil, pfrl := h.pfrl, pfrc := h.pfrc }

theorem MergeOKQ.push0 {η₁ η₂ : TEnv} (h : MergeOKQ cp f σ η₁ η₂) (s : Ty) :
    MergeOKQ cp f σ (η₁.push0 s) (η₂.push0 s) :=
  { wit := by simp [TEnv.push0, TEnv.ins, TEnv.insR, h.wit], prog := h.prog, tid := h.tid, fσ := h.fσ,
    σf := h.σf, sto := h.sto, ini := h.ini, rini := h.rini, pfr := h.pfr, seen := h.seen, box := h.box,
    cl := h.cl, inil := h.inil, rinil := h.rinil, pfrl := h.pfrl, pfrc := h.pfrc }

theorem rl_view (w : Word) : (rl f w).view = w.view := rfl

theorem Valid_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (t : Ty) :
    ∀ ws, Valid t ws → Valid t (ws.map (rl f)) := by
  induction t with
  | ptr μ u _ =>
    intro ws h; obtain ⟨a, ha⟩ := h; exact ⟨_, vals_rl_loc ha⟩
  | ptrOpt μ u _ =>
    intro ws h; rcases h with h | ⟨a, ha⟩
    · exact Or.inl (vals_rl_null.2 h)
    · exact Or.inr ⟨_, vals_rl_loc ha⟩
  | loc μ u _ =>
    intro ws h; rcases h with h | ⟨a, ha⟩
    · exact Or.inl (vals_rl_null.2 h)
    · exact Or.inr ⟨_, vals_rl_loc ha⟩
  | prod a b iha ihb =>
    intro ws h n hn
    obtain ⟨h1, h2⟩ := h n hn
    exact ⟨by rw [← List.map_take]; exact iha _ h1, by rw [← List.map_drop]; exact ihb _ h2⟩
  | sum a b iha ihb =>
    intro ws h
    rcases h with h | ⟨j, p, arm, hd, harm, ⟨hp1, hp2, hp3⟩, ⟨q, hq, hv⟩, hA, hB⟩
    · exact Or.inl h
    refine Or.inr ⟨j, p.map (rl f), arm, by rw [decodeArm_rl, hd]; rfl, harm, ⟨by simpa using hp1, ?_, ?_⟩,
      ⟨q.map (rl f), by rw [encodeArm_rl, hq]; rfl, by simp only [VEq] at hv ⊢; rw [vals_rl, vals_rl, hv]⟩,
      fun hj => ?_, fun hj => ?_⟩
    · intro hk; obtain ⟨w, adr, rfl, hw⟩ := hp2 hk
      exact ⟨rl f w, _, rfl, rl_val_loc hw⟩
    · intro hk; obtain ⟨w, rfl, hw⟩ := hp3 hk
      refine ⟨rl f w, rfl, ?_⟩
      rcases hw with hw | ⟨adr, hw⟩
      · exact Or.inl (by simp [rl, rlv, hw])
      · exact Or.inr ⟨_, rl_val_loc hw⟩
    · obtain ⟨q, h1, h2, h3, h4⟩ := hA hj
      exact ⟨q.map (rl f), by rw [ofArm_rl, h1]; rfl, fun us hu => by simpa using h2 us hu, h3, iha _ h4⟩
    · obtain ⟨q, h1, h2, h3, h4⟩ := hB hj
      exact ⟨q.map (rl f), by rw [ofArm_rl, h1]; rfl, fun us hu => by simpa using h2 us hu, h3, ihb _ h4⟩
  | refine t ψ ih => intro ws h; exact ih ws h
  | iall t ih => intro ws h; exact ih ws h
  | iex t ih => intro ws h; exact ih ws h
  | mu t ih => intro ws h; exact ih ws h
  | tex κ t ih => intro ws h; exact ih ws h
  | void => intro ws h; exact h
  | _ => intro ws h; trivial

theorem ShapeC_rl {t : Ty} {ws : List Word} (h : ShapeC t ws) : ShapeC t (ws.map (rl f)) :=
  fun us hu => by simpa using h us hu

end
end TermSound.Flat
