import WeakCore.Lift
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem ownW_lift (h1 : ∀ m, τ (σ m) = m) (h2 : ∀ m, σ (τ m) = m) (g : WeakMem.AllocLabel → WeakMem.AllocLabel) (μ : Mode)
    (ws : List Word) (h : μ = .own → g = σ) :
    Res.sw τ (ownW μ ws) = ownW μ (ws.map (rl g)) := by
  cases μ with
  | own => rw [h rfl]; exact ownW_sw (cp := fun _ => False) (fun m _ => h1 m) (fun m _ => h2 m) .own ws (fun _ _ _ _ h => h)
  | pub => exact ownW_sw (cp := fun _ => True) (f := g) (fun _ h => absurd trivial h) (fun _ h => absurd trivial h) .pub ws (fun e => by cases e)
  | rgn r =>
    exact ownW_sw (cp := fun _ => True) (f := g) (fun _ h => absurd trivial h) (fun _ h => absurd trivial h) (.rgn r) ws (fun e => by cases e)

/-- Position 0 of a single loc word: `σ`, or the copy of an exempt `Cp` label. -/
theorem gc0 {T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {E : TEnv}
    (hTx : ∀ k rt ws, ExS cpy σ Cp bv E ws (T k rt ws)) (t : Ty) (rt : Shp) {w : Word} {a : WeakMem.Address}
    {g : Nat} (hv : w.val = .loc a g) :
    gc cpy σ Cp bv T TU E t rt [w] 0 = σ ∨
      (gc cpy σ Cp bv T TU E t rt [w] 0 = cpy ∧ Cp a.label ∧ ¬ Fr1 E a.label w.view) ∨
      ∃ k, gc cpy σ Cp bv T TU E t rt [w] 0 = fun y => bv y k := by
  rcases gc_ExS t T TU E rt [w] hTx 0 with h | ⟨h1, h2⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2 w a g rfl hv⟩)
  · exact Or.inr (Or.inr h)

theorem modeOK_lift {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) {l : WeakMem.AllocLabel} {c : Cell}
    {ws : List Word} (hF : ∃ f, η₁.pfr l = some f ∧ (η₁.seen l ∨ ∀ w ∈ ws, f ≤ w.view))
    (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) :
    ModeOK η₂.tid η₂.pfr η₂.seen .pub (σ l) c (rlI G ws) := by
  obtain ⟨f, hf, hs⟩ := hF
  exact ⟨f, hm.pfr _ _ hf, hs.imp (hm.seen _) (fun hv => rlI_views G hv)⟩

theorem modeOK_cpy {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) {l : WeakMem.AllocLabel} (hc : Cp l)
    {c : Cell} (ws : List Word) : ModeOK η₂.tid η₂.pfr η₂.seen .pub (cpy l) c ws := by
  obtain ⟨f, hf, hle⟩ := hm.cpfr l hc
  exact ⟨f, hf, Or.inr (fun w _ => hle w.view)⟩

/-- The ♭ pub reference at a non-exempt position is fresh. -/
theorem fresh_of_nexm {η₁ E : TEnv} (hE : SameV E η₁)
    (hm : ∀ l c, η₁.sto l = some c → c.owner = some η₁.tid → (∃ q, η₁.pfr l = some q) → Cp l)
    {ws : List Word} {a : WeakMem.Address} {c : Cell} {bk : Prop}
    (h1 : ws.map (·.val) = [.loc a 0]) (h3 : η₁.sto a.label = some c)
    (hmo : ModeOKb η₁.tid η₁.pfr η₁.seen bk .pub a.label c ws) (hx : ¬ exmW Cp E ws) :
    ∃ f, η₁.pfr a.label = some f ∧ (η₁.seen a.label ∨ ∀ w ∈ ws, f ≤ w.view) := by
  obtain ⟨f, hf, hs | hv | ⟨ho, -⟩⟩ := hmo
  · exact ⟨f, hf, Or.inl hs⟩
  · exact ⟨f, hf, Or.inr hv⟩
  · have hc := hm _ _ h3 ho ⟨f, hf⟩
    rcases Classical.em (FreshW E ws) with hF | hn
    · obtain ⟨f', hf', hs'⟩ := hF a h1
      obtain ⟨hb, hp, hse⟩ := hE
      rw [hp] at hf'; rw [hse] at hs'
      exact ⟨f', hf', hs'⟩
    · exact absurd ⟨a, h1, hc, hn⟩ hx

theorem pubG_of_exm {E : TEnv} {ws : List Word} (hx : exmW Cp E ws) : pubG cpy σ Cp E ws 0 = cpy := by
  simp [pubG, hx]

theorem pubG_of_nexm {E : TEnv} {ws : List Word} (hx : ¬ exmW Cp E ws) : pubG cpy σ Cp E ws = fun _ => σ := by
  funext i; simp [pubG, hx]

end
end TermSound.Flat
