/-
# TermCut — S7e (shared-label transfer) and S7a (global environment, cuts)

Scratch module (stage B, S7).  Proof-only; nothing here changes stage A.

* **S7e.** `VR_transfer` (TermStep, B.3) needs `Incl η₁ η₂`: `η₂` contains
  *all* of `η₁`'s store typing.  A writer's environment holds its private
  cells, which no other thread's cut contains, so that is never available
  between threads.  `VR_transferS` needs `η₂` to contain only `η₁`'s
  **shared** cells (those with a frontier), at the price of a stronger type
  condition `noOR` (no `own` *and* no `rgn` reference: a region reference
  reads `sto` without a frontier).
* **S7a.** `GEnv`, `Shared`, `InCut`, `Cut`; `Cut` restricts only `sto`
  (`ini`, `pfr`, `box` are the global ones), so every cut contains every
  other cut's shared part (`InclS_cut`) and grows with `E_g` (`Cut_le`).
  The step relation `GFoot` (global reading of S6's `EFoot`), `Cut_self`, `Cut_other`.
* **B4 §3.2.**  `VR_transferL`: `VR` moves to an environment agreeing only at
  the labels `L` the words name (`LabIn`; `decodeArm`/`ofArm` name no new
  label), box payloads closed in `L`, `ini` upward at `L`.  `wordOK_back`
  (the frozen-future pull-back): a word typed in `E2 ⊇ E0` at a `.one` access
  (`Bnd_atOff_oneAt`) is typed in `E0`, splicing an `E0`-value of its segment
  around it (`TearOK`, `Valid_tear`).

Build: LEAN_PATH=build lean -o build/TermCut.olean TermCut.lean
-/
import WeakCore.TermTyped

namespace TermCut
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## S7e (1) The type condition -/

/-- No `own` and no `rgn` reference is reachable by `VR` (which does not
descend into a reference's target).  Type variables are free: `VR` reads
them through the relations, which the transfer carries (`hr`, `hur`). -/
def noOR : Ty → Bool
  | .ptr .pub _    => true
  | .ptr _ _       => false
  | .ptrOpt .pub _ => true
  | .ptrOpt _ _    => false
  | .loc .pub _    => true
  | .loc _ _       => false
  | .prod a b      => noOR a && noOR b
  | .sum a b       => noOR a && noOR b
  | .array _ t     => noOR t
  | .mu t          => noOR t
  | .tex _ t       => noOR t
  | .iall t        => noOR t
  | .iex t         => noOR t
  | .refine t _    => noOR t
  | _              => true

theorem noOR_ptr {μ : Mode} {u : Ty} (h : noOR (.ptr μ u) = true) : μ = .pub := by
  cases μ <;> simp_all [noOR]
theorem noOR_ptrOpt {μ : Mode} {u : Ty} (h : noOR (.ptrOpt μ u) = true) : μ = .pub := by
  cases μ <;> simp_all [noOR]
theorem noOR_loc {μ : Mode} {u : Ty} (h : noOR (.loc μ u) = true) : μ = .pub := by
  cases μ <;> simp_all [noOR]

/-- A `pub` reference's `ModeOK` gives the cell a frontier. -/
theorem ModeOK_pub_pfr {i : Nat} {P : AllocLabel → Option Ts} {S : AllocLabel → Prop} {l : AllocLabel}
    {c : Cell} {ws : List Word} (h : ModeOK i P S .pub l c ws) : ∃ f, P l = some f :=
  let ⟨f, hf, _⟩ := h; ⟨f, hf⟩

/-- `ModeOK .pub` with another thread id and larger frontier/seen maps. -/
theorem ModeOK_pub_move {i j : Nat} {P P' : AllocLabel → Option Ts} {S S' : AllocLabel → Prop}
    (hP : ∀ l f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l) {l : AllocLabel} {c c' : Cell}
    {ws : List Word} (h : ModeOK i P S .pub l c ws) : ModeOK j P' S' .pub l c' ws := by
  obtain ⟨f, h1, h2⟩ := h
  exact ⟨f, hP l f h1, h2.imp (hS l) id⟩

/-! ## S7e (2) `VR` / `VRR` transfer on shared labels -/

/-- Pointwise `selIni` monotonicity (one label). -/
theorem TEnv.selIni_le_one {η₁ η₂ : TEnv} (hw : η₁.wit = η₂.wit) {l : AllocLabel}
    (hi : η₁.ini l ≤ η₂.ini l) (hri : η₁.rini l ≤ η₂.rini l) (t : Ty) : η₁.selIni t l ≤ η₂.selIni t l := by
  unfold TEnv.selIni; rw [TEnv.ownTop_congr hw t]; split
  · simp only; omega
  · exact hi

/-- **Transfer of `VR` along the shared part.**  `η₂` need contain only the
cells of `η₁` that have a frontier (`hs`); `tid` is free (no `own`), and no
region reference reads a frontier-less cell (`noOR`). -/
theorem VR_transferS : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    noOR t = true →
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) →
    η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    (∀ l c f, η₁.sto l = some c → η₁.pfr l = some f → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l, η₁.rini l ≤ η₂.rini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    VR ρ η₁ t rt ws → VR ρ η₂ t rt ws
  | .tvar k, η₁, η₂, ρ, rt, ws, _, hr, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VR, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      exact ⟨VR_transferS t η₁ η₂ ρ rt ws hn hr hur hw hp hs hi hri hP hS hBx hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR_transferS b η₁ η₂ (vcons w ρ) rb ws hn hr hur hw hp hs hi hri hP hS hBx h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR, Bool.and_eq_true] at hn
      simp only [VR] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn' => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn'
      exact ⟨e1, VR_transferS a η₁ η₂ ρ _ _ hn.1 hr hur hw hp hs hi hri hP hS hBx e2,
        VR_transferS b η₁ η₂ ρ _ _ hn.2 hr hur hw hp hs hi hri hP hS hBx e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR, Bool.and_eq_true] at hn
      simp only [VR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn', hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn', hsB,
          hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ h2, h3⟩) id,
          fun hj => ⟨fun e => VR_transferS a η₁ η₂ ρ _ _ hn.1 hr hur hw hp hs hi hri hP hS hBx ((hA hj).1 e),
            fun e => ?_⟩,
          fun hj => ⟨fun e => VR_transferS b η₁ η₂ ρ _ _ hn.2 hr hur hw hp hs hi hri hP hS hBx ((hA' hj).1 e),
            fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_transferS a η₁.unsee η₂.unsee ρ _ _ hn.1 hur hur hw hp hs hi hri hP
            (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_transferS b η₁.unsee η₂.unsee ρ _ _ hn.2 hur hur hw hp hs hi hri hP
            (fun _ h => h.elim) hBx hv⟩
      · refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VR_transferS a η₁ η₂ ρ _ _ hn.1 hr hur hw hp hs hi hri hP hS hBx hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VR_transferS b η₁ η₂ ρ _ _ hn.2 hr hur hw hp hs hi hri hP hS hBx hv⟩
  | .code a b _, η₁, η₂, ρ, rt, ws, _, _, _, hw, hp, _, _, _, _, _, _, hv => by
      simp only [VR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR_transferS b (η₁.push0 s) (η₂.push0 s) ρ rb ws hn
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp hs hi hri hP hS hBx h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, hn, _, _, hw, _, hs, _, _, hP, hS, _, hv => by
      have hμ := noOR_ptr hn; subst hμ
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
      exact ⟨a, c, h1, h2, hs _ _ _ h3 hf, hw ▸ h4, ModeOK_pub_move hP hS h5, h6⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, hn, _, _, hw, _, hs, _, _, hP, hS, _, hv => by
      have hμ := noOR_ptrOpt hn; subst hμ
      simp only [VR] at hv ⊢
      rcases hv with hn0 | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn0
      · obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
        exact Or.inr ⟨a, c, h1, h2, hs _ _ _ h3 hf, hw ▸ h4, ModeOK_pub_move hP hS h5, h6⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, hn, _, _, hw, _, hs, hi, _, hP, hS, _, hv => by
      have hμ := noOR_loc hn; subst hμ
      simp only [VR] at hv ⊢
      rcases hv with hn0 | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn0.1, hw ▸ hn0.2⟩
      · obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
        exact Or.inr ⟨a, c, U, h1, hs _ _ _ h3 hf, h4, hw ▸ hF, ModeOK_pub_move hP hS h5, IniAt_mono hi h6⟩
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .opq _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tid, _, _, _, _, _, _, _, _, _, _, hs, _, _, hP, hS, _, hv => by
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h3, h4, h5⟩ := hv
      obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
      exact ⟨a, c, h1, hs _ _ _ h3 hf, h4, ModeOK_pub_move hP hS h5⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simp [VR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .mu b, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      rw [← hw]
      refine VR_transferS b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b)))
        ρ rt ws hn (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp hs hi hri hP hS hBx hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      exact fun n => VR_transferS b η₁ η₂ (vcons n ρ) rt ws hn hr hur hw hp hs hi hri hP hS hBx (hv n)

/-! ## B4 §3.2 `VR` transfer on the labels the words name -/

/-- Every `loc` word of `ws` names a label in `L`. -/
def LabIn (L : AllocLabel → Prop) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∀ x g, w.val = .loc x g → L x.label

theorem LabIn_take {L : AllocLabel → Prop} {ws : List Word} (h : LabIn L ws) (n : Nat) :
    LabIn L (ws.take n) := fun w hw => h w (List.mem_of_mem_take hw)

theorem LabIn_drop {L : AllocLabel → Prop} {ws : List Word} (h : LabIn L ws) (n : Nat) :
    LabIn L (ws.drop n) := fun w hw => h w (List.mem_of_mem_drop hw)

theorem LabIn_one {L : AllocLabel → Prop} {ws : List Word} {a : Address} {g : Nat} (h : LabIn L ws)
    (hv : ws.map (·.val) = [.loc a g]) : L a.label := by
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩ <;> simp at hv
  exact h w (by simp) a g hv

theorem LabIn_nil (L : AllocLabel → Prop) : LabIn L [] := fun _ h => by simp at h

theorem LabIn_cst {L : AllocLabel → Prop} (v : WeakMem.Val) (hv : ∀ x g, v ≠ .loc x g) : LabIn L [cst v] := by
  intro w hw x g hx
  simp at hw; subst hw; exact absurd hx (hv x g)

/-- A word with another tag on the same `loc` label. -/
theorem LabIn_retag {L : AllocLabel → Prop} {w : Word} {a : Address} {g k : Nat} (hp : LabIn L [w])
    (hw : w.val = .loc a g) : LabIn L [{ w with val := .loc a k }] := by
  intro w' hw' x g' hx
  simp at hw'; subst hw'; simp at hx
  obtain ⟨rfl, -⟩ := hx
  exact hp w (by simp) a g hw

/-- `encodeArm` names no new label. -/
theorem LabIn_encodeArm {L : AllocLabel → Prop} {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) (hp : LabIn L p) : LabIn L q := by
  unfold encodeArm at h
  split at h
  · cases harm : as[j]? <;> simp only [harm, bind, Option.bind] at h
    · contradiction
    split at h
    · split at h
      · simp at h; subst h; exact LabIn_retag hp ‹_›
      · split at h
        · simp at h; subst h; exact LabIn_cst _ (by simp)
        · contradiction
      · contradiction
    · split at h
      · simp at h; subst h; exact LabIn_retag hp ‹_›
      · split at h
        · simp at h; subst h; exact LabIn_cst _ (by simp)
        · contradiction
      · contradiction
    · simp at h; subst h; exact LabIn_cst _ (by simp)
    · contradiction
  · split at h
    · simp at h; subst h
      intro w hw x g hx; simp at hw; rcases hw with rfl | rfl <;> simp [cst, Promises.TVal.mk0] at hx
    · simp at h; subst h
      intro w' hw' x g hx; simp at hw'
      rcases hw' with rfl | rfl
      · simp [cst, Promises.TVal.mk0] at hx
      · exact hp _ (by simp) x g hx
    · contradiction
  · contradiction

theorem LabIn_ofArm {L : AllocLabel → Prop} {t : Ty} {j : Nat} {p q : List Word}
    (h : ofArm t j p = some q) (hp : LabIn L p) : LabIn L q := by
  unfold ofArm at h
  split at h
  · exact LabIn_encodeArm h hp
  · split at h
    · simp at h; subst h; exact hp
    · contradiction

/-- `decodeArm` names no new label. -/
theorem LabIn_decodeArm {L : AllocLabel → Prop} {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat}
    {p : List Word} (h : decodeArm tr as ws = some (j, p)) (hw : LabIn L ws) : LabIn L p := by
  unfold decodeArm at h
  split at h
  · split at h
    · rename_i g hv
      cases hg : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? <;> simp only [hg, bind, Option.bind] at h
      · contradiction
      simp [pure] at h
      obtain ⟨-, rfl⟩ := h
      exact LabIn_retag hw hv
    · rename_i j' _
      cases harm : as[j']? <;> simp only [harm, bind, Option.bind] at h
      · contradiction
      split at h
      · simp [pure] at h; obtain ⟨-, rfl⟩ := h; exact LabIn_nil L
      · simp [pure] at h; obtain ⟨-, rfl⟩ := h; exact LabIn_cst _ (by simp)
      · contradiction
    · contradiction
  · split at h
    · rename_i j' _
      cases harm : as[j']? <;> simp only [harm, bind, Option.bind] at h
      · contradiction
      split at h
      · simp [pure] at h; obtain ⟨-, rfl⟩ := h; exact LabIn_nil L
      · simp [pure] at h; obtain ⟨-, rfl⟩ := h
        intro w' hw' x g hx; simp at hw'; subst hw'; exact hw _ (by simp) x g hx
    · contradiction
  · contradiction

/-- `IniR` reads `ini` only at the label of the value's single `loc` word. -/
theorem IniR_monoL {ρ : Nat → Nat} {i₁ i₂ : AllocLabel → Nat} {ws : List Word}
    (h : ∀ a : Address, ws.map (·.val) = [.loc a 0] → i₁ a.label ≤ i₂ a.label) :
    ∀ {ψ : Pred}, IniR ρ i₁ ψ ws → IniR ρ i₂ ψ ws := by
  intro ψ
  induction ψ with
  | ini k => intro hv; simp only [IniR] at hv ⊢; intro a ha; exact Nat.le_trans (hv a ha) (h a ha)
  | and p q ihp ihq => intro hv; simp only [IniR] at hv ⊢; exact ⟨ihp hv.1, ihq hv.2⟩
  | _ => intro _; simp [IniR]

/-- `ModeOK .pub` moved along agreement at its own label. -/
theorem ModeOK_pub_moveL {i j : Nat} {P P' : AllocLabel → Option Ts} {S S' : AllocLabel → Prop}
    {l : AllocLabel} (hP : ∀ f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l) {c c' : Cell}
    {ws : List Word} (h : ModeOK i P S .pub l c ws) : ModeOK j P' S' .pub l c' ws := by
  obtain ⟨f, h1, h2⟩ := h
  exact ⟨f, hP f h1, h2.imp (hS l) id⟩

/-- **Transfer of `VR` along the labels the words name** (B4 §3.2).  As `VR_transferS`, but
`η₂` need agree with `η₁` (store at frontier cells, frontiers, boxes; `ini` only upward) only at
labels in `L`, which contains every label a word of the value names (`hn`) and, for a box at an
`L`-label, every label its payload names (`hcl`). -/
theorem VR_transferL (L : AllocLabel → Prop) : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp)
    (ws : List Word),
    noOR t = true → LabIn L ws → (∀ l B, L l → η₁.box l = some B → LabIn L B.pay) →
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) →
    η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    (∀ l c f, L l → η₁.sto l = some c → η₁.pfr l = some f → η₂.sto l = some c) →
    (∀ l, L l → η₁.ini l ≤ η₂.ini l) → (∀ l, L l → η₁.rini l ≤ η₂.rini l) → (∀ l f, L l → η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, L l → η₁.box l = some B → η₂.box l = some B) →
    VR ρ η₁ t rt ws → VR ρ η₂ t rt ws
  | .tvar k, η₁, η₂, ρ, rt, ws, _, _, _, hr, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VR, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      exact ⟨VR_transferL L t η₁ η₂ ρ rt ws hn hL hcl hr hur hw hp hs hi hri hP hS hBx hv.1,
        IniR_monoL (fun a ha => TEnv.selIni_le_one hw (hi _ (LabIn_one hL ha)) (hri _ (LabIn_one hL ha)) t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR_transferL L b η₁ η₂ (vcons w ρ) rb ws hn hL hcl hr hur hw hp hs hi hri hP hS hBx h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR, Bool.and_eq_true] at hn
      simp only [VR] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn' => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn'
      exact ⟨e1, VR_transferL L a η₁ η₂ ρ _ _ hn.1 (LabIn_take hL n) hcl hr hur hw hp hs hi hri hP hS hBx e2,
        VR_transferL L b η₁ η₂ ρ _ _ hn.2 (LabIn_drop hL n) hcl hr hur hw hp hs hi hri hP hS hBx e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR, Bool.and_eq_true] at hn
      simp only [VR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn', hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · have hLx : L x.label := LabIn_one hL hx
        have hLB : LabIn L B.pay := hcl _ _ hLx hB
        refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hLx hB, hn', hsB,
          hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ hLx h2, h3⟩) id,
          fun hj => ⟨fun e => VR_transferL L a η₁ η₂ ρ _ _ hn.1 hL hcl hr hur hw hp hs hi hri hP hS hBx ((hA hj).1 e),
            fun e => ?_⟩,
          fun hj => ⟨fun e => VR_transferL L b η₁ η₂ ρ _ _ hn.2 hL hcl hr hur hw hp hs hi hri hP hS hBx ((hA' hj).1 e),
            fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_transferL L a η₁.unsee η₂.unsee ρ _ _ hn.1 (LabIn_ofArm hq hLB) hcl
            hur hur hw hp hs hi hri hP (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_transferL L b η₁.unsee η₂.unsee ρ _ _ hn.2 (LabIn_ofArm hq hLB) hcl
            hur hur hw hp hs hi hri hP (fun _ h => h.elim) hBx hv⟩
      · have hLp : LabIn L p := LabIn_decodeArm hd hL
        refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VR_transferL L a η₁ η₂ ρ _ _ hn.1 (LabIn_ofArm hq hLp) hcl hr hur hw hp hs hi hri hP hS hBx hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VR_transferL L b η₁ η₂ ρ _ _ hn.2 (LabIn_ofArm hq hLp) hcl hr hur hw hp hs hi hri hP hS hBx hv⟩
  | .code a b _, η₁, η₂, ρ, rt, ws, _, _, _, _, _, hw, hp, _, _, _, _, _, _, hv => by
      simp only [VR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR_transferL L b (η₁.push0 s) (η₂.push0 s) ρ rb ws hn hL hcl
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp hs hi hri hP hS hBx h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, hn, hL, _, _, _, hw, _, hs, _, _, hP, hS, _, hv => by
      have hμ := noOR_ptr hn; subst hμ
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      have hLa : L a.label := LabIn_one hL h1
      obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
      exact ⟨a, c, h1, h2, hs _ _ _ hLa h3 hf, hw ▸ h4, ModeOK_pub_moveL (hP _ · hLa) hS h5, h6⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, hn, hL, _, _, _, hw, _, hs, _, _, hP, hS, _, hv => by
      have hμ := noOR_ptrOpt hn; subst hμ
      simp only [VR] at hv ⊢
      rcases hv with hn0 | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn0
      · have hLa : L a.label := LabIn_one hL h1
        obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
        exact Or.inr ⟨a, c, h1, h2, hs _ _ _ hLa h3 hf, hw ▸ h4, ModeOK_pub_moveL (hP _ · hLa) hS h5, h6⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, hn, hL, _, _, _, hw, _, hs, hi, _, hP, hS, _, hv => by
      have hμ := noOR_loc hn; subst hμ
      simp only [VR] at hv ⊢
      rcases hv with hn0 | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn0.1, hw ▸ hn0.2⟩
      · have hLa : L a.label := LabIn_one hL h1
        obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
        refine Or.inr ⟨a, c, U, h1, hs _ _ _ hLa h3 hf, h4, hw ▸ hF, ModeOK_pub_moveL (hP _ · hLa) hS h5, ?_⟩
        intro N e hc
        rcases h6 N e hc with h7 | ⟨us, j, o, h7, h8, h9, h10⟩
        · exact Or.inl h7
        · exact Or.inr ⟨us, j, o, h7, Nat.lt_of_lt_of_le h8 (hi _ hLa), h9, h10⟩
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .opq _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tid, _, _, _, _, _, _, hL, _, _, _, _, _, hs, _, _, hP, hS, _, hv => by
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h3, h4, h5⟩ := hv
      have hLa : L a := LabIn_one hL h1
      obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
      exact ⟨a, c, h1, hs _ _ _ hLa h3 hf, h4, ModeOK_pub_moveL (hP _ · hLa) hS h5⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simp [VR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .mu b, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      rw [← hw]
      refine VR_transferL L b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b)))
        ρ rt ws hn hL hcl (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp hs hi hri hP hS hBx hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, hn, hL, hcl, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VR] at hv ⊢
      exact fun n => VR_transferL L b η₁ η₂ (vcons n ρ) rt ws hn hL hcl hr hur hw hp hs hi hri hP hS hBx (hv n)


/-- `VR_transferS` for the resourceful `VRR` (resources unchanged). -/
theorem VRR_transferS : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (X : Res),
    noOR t = true →
    (∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S vs Y) → (∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S vs Y) →
    η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    (∀ l c f, η₁.sto l = some c → η₁.pfr l = some f → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l, η₁.rini l ≤ η₂.rini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    VRR ρ η₁ t rt ws X → VRR ρ η₂ t rt ws X
  | .tvar k, η₁, η₂, ρ, rt, ws, X, _, hr, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRR] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ X h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VRR] at hv ⊢
      exact ⟨VRR_transferS t η₁ η₂ ρ rt ws X hn hr hur hw hp hs hi hri hP hS hBx hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VRR_transferS b η₁ η₂ (vcons w ρ) rb ws X hn hr hur hw hp hs hi hri hP hS hBx h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR, Bool.and_eq_true] at hn
      simp only [VRR] at hv ⊢
      obtain ⟨ra, rb, h1, Ra, Rb, hR, hz, hf⟩ := hv
      refine ⟨ra, rb, h1, Ra, Rb, hR, hz, fun n hn' => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn'
      exact ⟨e1, VRR_transferS a η₁ η₂ ρ _ _ _ hn.1 hr hur hw hp hs hi hri hP hS hBx e2,
        VRR_transferS b η₁ η₂ ρ _ _ _ hn.2 hr hur hw hp hs hi hri hP hS hBx e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR, Bool.and_eq_true] at hn
      simp only [VRR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn', hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn', hsB,
          hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ h2, h3⟩) id,
          fun hj => ⟨fun e => VRR_transferS a η₁ η₂ ρ _ _ _ hn.1 hr hur hw hp hs hi hri hP hS hBx ((hA hj).1 e),
            fun e => ?_⟩,
          fun hj => ⟨fun e => VRR_transferS b η₁ η₂ ρ _ _ _ hn.2 hr hur hw hp hs hi hri hP hS hBx ((hA' hj).1 e),
            fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRR_transferS a η₁.unsee η₂.unsee ρ _ _ _ hn.1 hur hur hw hp hs hi hri hP
            (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRR_transferS b η₁.unsee η₂.unsee ρ _ _ _ hn.2 hur hur hw hp hs hi hri hP
            (fun _ h => h.elim) hBx hv⟩
      · refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VRR_transferS a η₁ η₂ ρ _ _ _ hn.1 hr hur hw hp hs hi hri hP hS hBx hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VRR_transferS b η₁ η₂ ρ _ _ _ hn.2 hr hur hw hp hs hi hri hP hS hBx hv⟩
  | .code a b _, η₁, η₂, ρ, rt, ws, X, _, _, _, hw, hp, _, _, _, _, _, _, hv => by
      simp only [VRR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VRR_transferS b (η₁.push0 s) (η₂.push0 s) ρ rb ws X hn
        (push0_rrs_mono hr) (push0_urrs_mono hur) ?_ hp hs hi hri hP hS hBx h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, X, hn, _, _, hw, _, hs, _, _, hP, hS, _, hv => by
      have hμ := noOR_ptr hn; subst hμ
      simp only [VRR] at hv ⊢
      obtain ⟨⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
      exact ⟨⟨a, c, h1, h2, hs _ _ _ h3 hf, hw ▸ h4, ModeOK_pub_move hP hS h5, h6⟩, hR⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, X, hn, _, _, hw, _, hs, _, _, hP, hS, _, hv => by
      have hμ := noOR_ptrOpt hn; subst hμ
      simp only [VRR] at hv ⊢
      obtain ⟨hn0 | ⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl hn0, hR⟩
      · obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
        exact ⟨Or.inr ⟨a, c, h1, h2, hs _ _ _ h3 hf, hw ▸ h4, ModeOK_pub_move hP hS h5, h6⟩, hR⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, X, hn, _, _, hw, _, hs, hi, _, hP, hS, _, hv => by
      have hμ := noOR_loc hn; subst hμ
      simp only [VRR] at hv ⊢
      obtain ⟨hn0 | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl ⟨hn0.1, hw ▸ hn0.2⟩, hR⟩
      · obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
        exact ⟨Or.inr ⟨a, c, U, h1, hs _ _ _ h3 hf, h4, hw ▸ hF, ModeOK_pub_move hP hS h5,
          IniAt_mono hi h6⟩, hR⟩
  | .mu b, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VRR] at hv ⊢
      rw [← hw]
      refine VRR_transferS b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b)))
        ρ rt ws X hn (push0_rrs_mono hr) (push0_urrs_mono hur) ?_ hp hs hi hri hP hS hBx hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, X, hn, hr, hur, hw, hp, hs, hi, hri, hP, hS, hBx, hv => by
      simp only [noOR] at hn
      simp only [VRR] at hv ⊢
      exact fun n => VRR_transferS b η₁ η₂ (vcons n ρ) rt ws X hn hr hur hw hp hs hi hri hP hS hBx (hv n)
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .opq _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR, VR] at hv ⊢; exact hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .tid, _, _, _, _, _, _, _, _, _, _, _, hs, _, _, hP, hS, _, hv => by
      simp only [VRR, VR] at hv ⊢
      obtain ⟨⟨a, c, h1, h3, h4, h5⟩, hR⟩ := hv
      obtain ⟨f, hf⟩ := ModeOK_pub_pfr h5
      exact ⟨⟨a, c, h1, hs _ _ _ h3 hf, h4, ModeOK_pub_move hP hS h5⟩, hR⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simp [VRR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv

/-- `noOR` from what `PubCpl` records (`noOwnIn`) plus region-freedom (an
interim scope fact before R2). -/
theorem noOR_of : ∀ (T : Ty) (ke : KEnv), Ty.noOwnIn ke T = true → rgnFree T = true → noOR T = true
  | .ptr μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.noOwnIn, rgnFree, noOR]
  | .ptrOpt μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.noOwnIn, rgnFree, noOR]
  | .loc μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.noOwnIn, rgnFree, noOR]
  | .prod a b, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨noOR_of a ke h1.1 h2.1, noOR_of b ke h1.2 h2.2⟩
  | .sum a b, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨noOR_of a ke h1.1 h2.1, noOR_of b ke h1.2 h2.2⟩
  | .array _ t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of t ke h1 h2
  | .mu t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of t _ h1 h2
  | .tex κ t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR, Bool.and_eq_true] at h1 h2 ⊢; exact noOR_of t _ h1.2 h2
  | .iall t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of t ke h1 h2
  | .iex t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of t ke h1 h2
  | .refine t _, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of t ke h1 h2
  | .intS _, _, _, _ | .int, _, _, _ | .tid, _, _, _ | .fix _ _, _, _, _ | .lanes _ _, _, _, _ | .unit, _, _, _
  | .void, _, _, _ | .share _, _, _, _ | .cap _ _, _, _, _ | .word _ _, _, _, _ | .tok _ _, _, _, _
  | .word2 _ _, _, _, _ | .tok2 _ _ _ _, _, _, _ | .epair _ _, _, _, _ | .tokE _ _ _, _, _, _
  | .tvar _, _, _, _ | .code _ _ _, _, _, _ | .opq _, _, _, _ => by simp [noOR]

/-! ## S7e (3) Wrappers: memory values (read at `CE η.unsee`) -/

/-- What the shared transfer needs: same program; `η₂` contains `η₁`'s cells
**that have a frontier**, and `η₁`'s initialised counts, frontiers and boxes.
`tid` and `seen` are free. -/
structure InclS (η₁ η₂ : TEnv) : Prop where
  prog : η₁.prog = η₂.prog
  sto : ∀ l c f, η₁.sto l = some c → η₁.pfr l = some f → η₂.sto l = some c
  ini : ∀ l, η₁.ini l ≤ η₂.ini l
  pfr : ∀ l f, η₁.pfr l = some f → η₂.pfr l = some f
  box : ∀ l B, η₁.box l = some B → η₂.box l = some B
  rini : ∀ l, η₁.rini l ≤ η₂.rini l

theorem InclS.of_incl {η₁ η₂ : TEnv} (h : Incl η₁ η₂) : InclS η₁ η₂ :=
  ⟨h.prog, fun l c _ hc _ => h.sto l c hc, h.ini, h.pfr, h.box, h.rini⟩

theorem InclS.refl (η : TEnv) : InclS η η := InclS.of_incl (Incl.refl η)

theorem InclS.trans {η₁ η₂ η₃ : TEnv} (h1 : InclS η₁ η₂) (h2 : InclS η₂ η₃) : InclS η₁ η₃ :=
  ⟨h1.prog.trans h2.prog, fun l c f hc hf => h2.sto l c f (h1.sto l c f hc hf) (h1.pfr l f hf),
    fun l => Nat.le_trans (h1.ini l) (h2.ini l), fun l f h => h2.pfr l f (h1.pfr l f h),
    fun l B h => h2.box l B (h1.box l B h), fun l => Nat.le_trans (h1.rini l) (h2.rini l)⟩

theorem noOR_seg {T S : Ty} {b : Nat} (hs : SegOf T b S) (h : noOR T = true) : noOR S = true := by
  rcases hs with ⟨-, rfl, -⟩ | ⟨N, us, j, rfl, -⟩
  · exact h
  · simpa [noOR] using h

theorem noOR_array {N : Idx} {e : Ty} (h : noOR (.array N e) = true) : noOR e = true := by
  simpa [noOR] using h

theorem ValOf_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {ws : List Word} (h : ValOf η₁ T ws) : ValOf η₂ T ws :=
  ⟨VR_transferS T (CE η₁.unsee) (CE η₂.unsee) _ _ _ hT (fun _ _ _ h => h) (fun _ _ _ h => h) rfl hE.prog
    hE.sto hE.ini hE.rini hE.pfr (fun _ h => h) hE.box h.1, h.2⟩

theorem ValOfS_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {ws : List Word} (h : ValOfS η₁ T ws) : ValOfS η₂ T ws :=
  ⟨ValOf_transferS hE hT h.1, h.2⟩

theorem WordOK_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {o : Nat} {w : Word} (h : WordOK η₁ T o w) : WordOK η₂ T o w := by
  obtain ⟨b, S, ws, o', w0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨b, S, ws, o', w0, h1, ValOfS_transferS hE (noOR_seg h1 hT) h2, h3, h4, h5⟩

theorem PairOK_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {o : Nat} {w0 w1 : Word} (h : PairOK η₁ T o w0 w1) : PairOK η₂ T o w0 w1 := by
  obtain ⟨b, S, ws, o', x0, x1, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨b, S, ws, o', x0, x1, h1, ValOfS_transferS hE (noOR_seg h1 hT) h2, h3, h4, h5, h6, h7⟩

/-! ## B4 §3.2 The frozen-future pull-back -/

theorem SegOf_accs {T S : Ty} {b : Nat} (hs : SegOf T b S) : ∃ us, accs S = some us := by
  rcases hs with ⟨-, rfl, h⟩ | ⟨N, us, j, -, h, -⟩
  · exact Option.ne_none_iff_exists'.1 h
  · exact ⟨us, h⟩

theorem LabIn_of_get {L : AllocLabel → Prop} {ws : List Word}
    (h : ∀ (i : Nat) (w : Word), ws[i]? = some w → ∀ (x : Address) (g : Nat), w.val = .loc x g → L x.label) : LabIn L ws := by
  intro w hw x g hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
  exact h i w hi x g hx

theorem Bnd_cons {u : Acc} {us : List Acc} {k : Nat} (h : TermTear.Bnd us k) :
    TermTear.Bnd (u :: us) (k + u.size) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i + 1, by simp [nWords]; omega⟩

/-- Both edges of a `.one` unit are unit boundaries. -/
theorem Bnd_oneAt {us : List Acc} {j : Nat} (h : TermFul.OneAt us j) :
    TermTear.Bnd us j ∧ TermTear.Bnd us (j + 1) := by
  induction h with
  | here us => exact ⟨⟨0, by simp [nWords]⟩, ⟨1, by simp [nWords, Acc.size]⟩⟩
  | cons u _ ih =>
      refine ⟨Bnd_cons ih.1, ?_⟩
      have := Bnd_cons (u := u) ih.2
      rwa [Nat.add_right_comm] at this

theorem Bnd_embed {pre us post : List Acc} {k : Nat} (h : TermTear.Bnd us k) :
    TermTear.Bnd (pre ++ us ++ post) (nWords pre + k) := by
  obtain ⟨i, rfl⟩ := h
  rcases Nat.le_total i us.length with hi | hi
  · refine ⟨pre.length + i, ?_⟩
    rw [List.append_assoc, List.take_length_add_append, List.take_append_of_le_length hi,
      TermTear.nWords_append]
  · refine ⟨pre.length + us.length, ?_⟩
    rw [List.append_assoc, List.take_length_add_append, List.take_append_of_le_length (Nat.le_refl _),
      TermTear.nWords_append, List.take_of_length_le hi, List.take_of_length_le (Nat.le_refl _)]

/-- A `.one` unit of a component at offset `o` of a segment type: both edges of the word are unit
boundaries of the segment (the `hone` premise of `wordOK_back`, for a whole-cell segment). -/
theorem Bnd_atOff_oneAt {S U : Ty} {o j : Nat} {uS us : List Acc} (h : AtOff S o U)
    (hS : accs S = some uS) (hU : accs U = some us) (hj : TermFul.OneAt us j) :
    TermTear.Bnd uS (o + j) ∧ TermTear.Bnd uS (o + j + 1) := by
  obtain ⟨pre, post, rfl, rfl⟩ := AtOff_embed h hS hU
  obtain ⟨h1, h2⟩ := Bnd_oneAt hj
  exact ⟨Bnd_embed h1, by rw [Nat.add_assoc]; exact Bnd_embed h2⟩

/-- **The pull-back** (B4 §3.2): a word typed in `E2 ⊇ E0` is typed in `E0`, when it sits at a
`.one` access of its segment (`hone`: both of its edges are unit boundaries), the segment has an
`E0`-value (`hInh`) and is torn-read safe (`hTear`), and `E0` agrees with `E2` at the labels `L`
the word and that value name (store at frontier cells, frontiers, boxes; `ini` upward: residual
R3 restated as `hi`; box payloads closed in `L`: `hcl`, residual R2).  The `E2`-value of the
segment is replaced by the `E0`-value everywhere but at the word (`splice` twice), so the other
words' `E2`-only labels disappear. -/
theorem wordOK_back {E0 E2 : TEnv} {T : Ty} {o : Nat} {w : Word} (L : AllocLabel → Prop)
    (hI : InclS E0 E2) (hT : noOR T = true)
    (hs : ∀ l c f, L l → E2.sto l = some c → E2.pfr l = some f → E0.sto l = some c)
    (hi : ∀ l, L l → E2.ini l ≤ E0.ini l) (hP : ∀ l f, L l → E2.pfr l = some f → E0.pfr l = some f)
    (hb : ∀ l B, L l → E2.box l = some B → E0.box l = some B)
    (hri : ∀ l, L l → E2.rini l ≤ E0.rini l)
    (hcl : ∀ l B, L l → E2.box l = some B → LabIn L B.pay)
    (hTear : ∀ b S, SegOf T b S → TearOK S)
    (hInh : ∀ b S us, SegOf T b S → accs S = some us →
      ∃ ws, ValOf E0 S ws ∧ ws.length = nWords us ∧ LabIn L ws)
    (hone : ∀ b S us, SegOf T b S → accs S = some us → b ≤ o → o < b + nWords us →
      TermTear.Bnd us (o - b) ∧ TermTear.Bnd us (o - b + 1))
    (hloc : ∀ x g, w.val = .loc x g → L x.label)
    (h : WordOK E2 T o w) : WordOK E0 T o w := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, hval⟩, hsh⟩, hw0, hle, hbo⟩ := h
  obtain ⟨us, hus⟩ := SegOf_accs hseg
  have hl : ws.length = nWords us := hsh us hus
  obtain ⟨ws0, ⟨hv0, hV0⟩, hl0, hL0⟩ := hInh b S us hseg hus
  have ho' : o' < ws.length := by
    rcases Nat.lt_or_ge o' ws.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hw0; cases hw0
  obtain ⟨hb1, hb2⟩ := hone b S us hseg hus (by omega) (by omega)
  rw [show o - b = o' by omega] at hb1 hb2
  have hS := noOR_seg hseg hT
  have hv0' : VR (fun _ => 0) (CE E2.unsee) S (shp S) ws0 := (ValOf_transferS hI hS ⟨hv0, hV0⟩).1
  have hv1 := hTear b S hseg E2.unsee us (o' + 1) ws ws0 hus hb2 hvr hv0' hl hl0
  have hl1 : (TermTear.splice (o' + 1) ws ws0).length = nWords us := by
    rw [TermTear.splice_length (hl.trans hl0.symm)]; exact hl0
  have hv2 := hTear b S hseg E2.unsee us o' ws0 _ hus hb1 hv0' hv1 hl0 hl1
  have hV1 := TermTear.Valid_tear hus hb2 hval hV0 hl hl0
  have hV2 := TermTear.Valid_tear hus hb1 hV0 hV1 hl0 hl1
  have hl2 : (TermTear.splice o' ws0 (TermTear.splice (o' + 1) ws ws0)).length = nWords us := by
    rw [TermTear.splice_length (hl0.trans hl1.symm)]; exact hl1
  have hgetE : (TermTear.splice o' ws0 (TermTear.splice (o' + 1) ws ws0))[o']? = ws[o']? := by
    rw [TermTear.splice_get_ge (Nat.le_refl _) (by omega), TermTear.splice_get_lt (by omega) (by omega)]
  have hgetN : ∀ i, i ≠ o' → (TermTear.splice o' ws0 (TermTear.splice (o' + 1) ws ws0))[i]? = ws0[i]? := by
    intro i hne
    rcases Nat.lt_or_ge i o' with h1 | h1
    · rw [TermTear.splice_get_lt h1 (by omega)]
    · rw [TermTear.splice_get_ge h1 (by omega), TermTear.splice_get_ge (by omega) (by omega)]
  have hL2 : LabIn L (TermTear.splice o' ws0 (TermTear.splice (o' + 1) ws ws0)) := by
    refine LabIn_of_get fun i w' hw' x g hx => ?_
    by_cases hio : i = o'
    · subst i; rw [hgetE, hw0] at hw'; cases hw'
      exact hloc x g (hle.1 ▸ hx)
    · rw [hgetN i hio] at hw'
      exact hL0 w' (List.mem_of_getElem? hw') x g hx
  have hvr2 := VR_transferL L S (CE E2.unsee) (CE E0.unsee) (fun _ => 0) (shp S) _ hS hL2 hcl
    (fun _ _ _ h => h) (fun _ _ _ h => h) rfl hI.prog.symm hs hi hri hP (fun _ h => h) hb hv2
  refine ⟨b, S, _, o', w0, hseg, ⟨⟨hvr2, hV2⟩, fun us' hus' => ?_⟩, ?_, hle, hbo⟩
  · rw [hus] at hus'; cases hus'; exact hl2
  · rw [hgetE, hw0]

theorem BufOK_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {n : Nat} {vals : List Word} (h : BufOK η₁ n T vals) : BufOK η₂ n T vals := by
  obtain ⟨N, e, us, hTe, hu, hn, hl, hj⟩ := h
  subst hTe
  exact ⟨N, e, us, rfl, hu, hn, hl, fun j hjn => ValOf_transferS hE (noOR_array hT) (hj j hjn)⟩

theorem CellOK_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {n : Nat} {vals : List Word} (h : CellOK η₁ n T vals) : CellOK η₂ n T vals := by
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, ValOf_transferS hE hT h2⟩
  · exact Or.inr (BufOK_transferS hE hT h)

theorem ValOfR_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {ws : List Word} {R : Res} (h : ValOfR η₁ T ws R) : ValOfR η₂ T ws R :=
  ⟨VRR_transferS T (CE η₁.unsee) (CE η₂.unsee) _ _ _ _ hT (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl
    hE.prog hE.sto hE.ini hE.rini hE.pfr (fun _ h => h) hE.box h.1, h.2⟩

theorem BufOKR_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {n nr : Nat} {vals : List Word} {R : Res} (h : BufOKR η₁ n nr T vals R) : BufOKR η₂ n nr T vals R := by
  obtain ⟨N, e, us, Rs, hTe, hu, hn, hl, hRs, hR, hj⟩ := h
  subst hTe
  exact ⟨N, e, us, Rs, rfl, hu, hn, hl, hRs, hR,
    fun j Rj h1 h2 => ⟨(hj j Rj h1 h2).1, fun h3 => ValOfR_transferS hE (noOR_array hT) ((hj j Rj h1 h2).2 h3)⟩⟩

theorem CellOKR_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) {T : Ty} (hT : noOR T = true)
    {n nr : Nat} {vals : List Word} {R : Res} (h : CellOKR η₁ n nr T vals R) : CellOKR η₂ n nr T vals R := by
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, ValOfR_transferS hE hT h2⟩
  · exact Or.inr (BufOKR_transferS hE hT h)

/-- A value in the thread's own view (`EnvVal`, `seen` read) moves when `seen` grows. -/
theorem EnvVal_transferS {η₁ η₂ : TEnv} (hE : InclS η₁ η₂) (hS : ∀ l, η₁.seen l → η₂.seen l) {T : Ty}
    (hT : noOR T = true) {ws : List Word} (h : EnvVal η₁ T ws) : EnvVal η₂ T ws :=
  ⟨VR_transferS T (CE η₁) (CE η₂) _ _ _ hT (fun _ _ _ h => h) (fun _ _ _ h => h) rfl hE.prog
    hE.sto hE.ini hE.rini hE.pfr hS hE.box h.1, h.2⟩

/-! ## S7a The global environment and the cuts -/

/-- **The global ghost environment** (A-strict): one store typing
(type and allocator of every cell, fixed at allocation), one initialised count,
one frontier map (published, or planted when pending) and one box map. -/
structure GEnv where
  prog : Prog := []
  sto : AllocLabel → Option Cell := fun _ => none
  ini : AllocLabel → Nat := fun _ => 0
  /-- (rini, design (a′)) The owner's real initialised counts (`TEnv.rini`). -/
  rini : AllocLabel → Nat := fun _ => 0
  pfr : AllocLabel → Option Ts := fun _ => none
  box : AllocLabel → Option Box := fun _ => none
  /-- Ghost: thread `i`'s foreign
  promises (every outstanding promise of every other thread), its cut's `fp`. -/
  fpOf : Nat → List Ts := fun _ => []
  /-- (ownSeen, ghost) The labels published so far: set by `GEnv.post` where a thread step moves
  a frontier from none to some and marks the label seen (a `publish`; a plant marks nothing seen).
  The `SysInvN` clause `ownPub`: no thread holds the own key of a published label. -/
  pubd : AllocLabel → Prop := fun _ => False

/-- `l` is shared: it has a frontier (published, or pending with a planted one). -/
def GEnv.Shared (Eg : GEnv) (l : AllocLabel) : Prop := ∃ f, Eg.pfr l = some f

/-- `l` is in thread `i`'s cut: one of `i`'s cells, or a shared cell. -/
def GEnv.InCut (Eg : GEnv) (i : Nat) (l : AllocLabel) : Prop :=
  ∃ c, Eg.sto l = some c ∧ (c.owner = some i ∨ Eg.Shared l)

/-- `E_g` grows. -/
structure GEnv.le (Eg Eg' : GEnv) : Prop where
  prog : Eg'.prog = Eg.prog
  sto : ∀ l c, Eg.sto l = some c → Eg'.sto l = some c
  ini : ∀ l, Eg.ini l ≤ Eg'.ini l
  pfr : ∀ l f, Eg.pfr l = some f → Eg'.pfr l = some f
  box : ∀ l B, Eg.box l = some B → Eg'.box l = some B
  rini : ∀ l, Eg.rini l ≤ Eg'.rini l

theorem GEnv.le.refl (Eg : GEnv) : Eg.le Eg :=
  ⟨rfl, fun _ _ h => h, fun _ => Nat.le_refl _, fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

theorem GEnv.le.trans {E1 E2 E3 : GEnv} (a : E1.le E2) (b : E2.le E3) : E1.le E3 :=
  ⟨b.prog.trans a.prog, fun l c h => b.sto l c (a.sto l c h), fun l => Nat.le_trans (a.ini l) (b.ini l),
    fun l f h => b.pfr l f (a.pfr l f h), fun l B h => b.box l B (a.box l B h),
    fun l => Nat.le_trans (a.rini l) (b.rini l)⟩

open Classical in
/-- The cut's store typing: `E_g`'s cell where `l` is in `i`'s cut. -/
noncomputable def cutSto (Eg : GEnv) (i : Nat) (l : AllocLabel) : Option Cell :=
  if Eg.InCut i l then Eg.sto l else none

/-- **Thread `i`'s environment**, the part `MemInv`/`MemHeld`/`PromCr` read
(`CE`-shaped: no type variables).  Only `sto` is cut; `ini`, `pfr`, `box` are
the global maps (at labels outside the cut they are never read by `VR`, and
`FreshLP`'s `ini = 0`, `pfr = none` at `i`'s fresh labels hold globally:
nobody else allocates or publishes there).  `seen` is the thread's own. -/
noncomputable def Cut (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : TEnv :=
  { prog := Eg.prog, sto := cutSto Eg i, tid := i, ini := Eg.ini, rini := Eg.rini, pfr := Eg.pfr, seen := S, box := Eg.box,
    fp := Eg.fpOf i }

@[simp] theorem Cut_prog (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).prog = Eg.prog := rfl
@[simp] theorem Cut_tid (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).tid = i := rfl
@[simp] theorem Cut_ini (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).ini = Eg.ini := rfl
@[simp] theorem Cut_pfr (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).pfr = Eg.pfr := rfl
@[simp] theorem Cut_seen (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).seen = S := rfl
@[simp] theorem Cut_box (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).box = Eg.box := rfl
theorem Cut_sto (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).sto = cutSto Eg i := rfl
@[simp] theorem Cut_rini (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).rini = Eg.rini := rfl
@[simp] theorem Cut_fp (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : (Cut Eg i S).fp = Eg.fpOf i := rfl

/-- A cut is `CE`-shaped: it is its own code view. -/
theorem CE_Cut (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : CE (Cut Eg i S) = Cut Eg i S := rfl

theorem cutSto_some {Eg : GEnv} {i : Nat} {l : AllocLabel} {c : Cell} :
    cutSto Eg i l = some c ↔ Eg.sto l = some c ∧ (c.owner = some i ∨ Eg.Shared l) := by
  unfold cutSto
  by_cases h : Eg.InCut i l
  · simp only [h, ↓reduceIte]
    obtain ⟨c', h1, h2⟩ := h
    constructor
    · intro e; rw [h1] at e; cases e; exact ⟨h1, h2⟩
    · exact fun ⟨e, _⟩ => e
  · simp only [h, ↓reduceIte]
    exact ⟨fun e => (by cases e), fun ⟨e, ho⟩ => absurd ⟨c, e, ho⟩ h⟩

/-- An own cell of `i` is in `i`'s cut. -/
theorem cutSto_own {Eg : GEnv} {i : Nat} {l : AllocLabel} {c : Cell} (h : Eg.sto l = some c)
    (ho : c.owner = some i) : cutSto Eg i l = some c := cutSto_some.2 ⟨h, Or.inl ho⟩

/-- A shared cell is in every cut. -/
theorem cutSto_shared {Eg : GEnv} {i : Nat} {l : AllocLabel} {c : Cell} (h : Eg.sto l = some c)
    (hs : Eg.Shared l) : cutSto Eg i l = some c := cutSto_some.2 ⟨h, Or.inr hs⟩

/-- Another thread's private cell (no frontier) is in no other cut. -/
theorem cutSto_priv {Eg : GEnv} {i j : Nat} {l : AllocLabel} {c : Cell} (h : Eg.sto l = some c)
    (ho : c.owner = some j) (hij : i ≠ j) (hp : Eg.pfr l = none) : cutSto Eg i l = none := by
  cases e : cutSto Eg i l with
  | none => rfl
  | some c' =>
    obtain ⟨h1, h2⟩ := cutSto_some.1 e
    rw [h] at h1; cases h1
    rcases h2 with h2 | ⟨f, hf⟩
    · rw [ho] at h2; cases h2; exact absurd rfl hij
    · rw [hp] at hf; cases hf

/-- A cut agrees with `E_g` where it is defined. -/
theorem cutSto_sub {Eg : GEnv} {i : Nat} {l : AllocLabel} {c : Cell} (h : cutSto Eg i l = some c) :
    Eg.sto l = some c := (cutSto_some.1 h).1

/-- **Every cut contains every other cut's shared part** (with any `tid`, any
`seen`): what moves a message typed by its writer into a reader's cut. -/
theorem InclS_cut (Eg : GEnv) (i j : Nat) (S S' : AllocLabel → Prop) : InclS (Cut Eg i S) (Cut Eg j S') :=
  ⟨rfl, fun _ _ f hc hf => cutSto_shared (cutSto_sub hc) ⟨f, hf⟩, fun _ => Nat.le_refl _,
    fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

/-- **A cut grows with `E_g`** (and with the thread's `seen`): `i`'s frame and
memory facts move along `Incl` (`Ext` once coherence is added). -/
theorem Cut_le {Eg Eg' : GEnv} (h : Eg.le Eg') (i : Nat) {S S' : AllocLabel → Prop} (hS : ∀ l, S l → S' l) :
    Incl (Cut Eg i S) (Cut Eg' i S') ∧ (Cut Eg' i S').tid = (Cut Eg i S).tid ∧
      (∀ l, (Cut Eg i S).seen l → (Cut Eg' i S').seen l) := by
  refine ⟨⟨h.prog.symm, fun l c hc => ?_, h.ini, h.pfr, h.box, h.rini⟩, rfl, hS⟩
  obtain ⟨h1, h2⟩ := cutSto_some.1 hc
  refine cutSto_some.2 ⟨h.sto l c h1, h2.imp id fun ⟨f, hf⟩ => ⟨f, h.pfr l f hf⟩⟩

/-- A message of a cell shared in `E_g`, typed in its writer's cut, is typed in
every cut (the cell's type is `noOR`). -/
theorem WordOK_cut {Eg : GEnv} {i j : Nat} {S S' : AllocLabel → Prop} {T : Ty} (hT : noOR T = true)
    {o : Nat} {w : Word} (h : WordOK (Cut Eg i S) T o w) : WordOK (Cut Eg j S') T o w :=
  WordOK_transferS (InclS_cut Eg i j S S') hT h

theorem CellOKR_cut {Eg : GEnv} {i j : Nat} {S S' : AllocLabel → Prop} {T : Ty} (hT : noOR T = true)
    {n nr : Nat} {vals : List Word} {R : Res} (h : CellOKR (Cut Eg i S) n nr T vals R) :
    CellOKR (Cut Eg j S') n nr T vals R :=
  CellOKR_transferS (InclS_cut Eg i j S S') hT h

/-- A certificate environment `E2` (from the typed run) moves its
typing of a shared cell's message into any cut, provided its frontiers and the
cells carrying them are `E_g`'s (its new cells are the thread's fresh labels,
which have no frontier) and its counts and boxes are below `E_g`'s. -/
theorem InclS_cert_cut {Eg : GEnv} {j : Nat} {S' : AllocLabel → Prop} {E2 : TEnv}
    (hp : E2.prog = Eg.prog)
    (hsto : ∀ l c f, E2.sto l = some c → E2.pfr l = some f → Eg.sto l = some c)
    (hpfr : ∀ l f, E2.pfr l = some f → Eg.pfr l = some f)
    (hini : ∀ l, E2.ini l ≤ Eg.ini l) (hbox : ∀ l B, E2.box l = some B → Eg.box l = some B)
    (hrini : ∀ l, E2.rini l ≤ Eg.rini l) :
    InclS E2 (Cut Eg j S') :=
  ⟨hp, fun l c f hc hf => cutSto_shared (hsto l c f hc hf) ⟨f, hpfr l f hf⟩, hini, hpfr, hbox, hrini⟩

/-! ## S7a (2) A step of thread `g.i` on `E_g`, matching S6's `EFoot`

S6 exposes a step's effect on the stepping thread's environment as the
relation `EFoot g E E' s s'` (TermStep, after `ThInvM`), not as a list of
deltas.  So the global step is a relation too: `GFoot`, field for field the
global reading of `EFoot`.  From the stepping thread's cut `Cut E_g g.i S` and
S6's witness `E'`, `GEnv.post` builds the new `E_g` (`E'`'s maps, with `sto`
and `box` taken from `E'` exactly at the step's fresh labels); `EFoot_post` shows it is a
`GFoot` step, `Cut_self` that `E'` is exactly the new cut, `Cut_other` that every
other cut only grows, by exactly the newly published cell. -/

/-- `l` is one of thread `i`'s cells in `E_g`. -/
def GEnv.OwnAt (Eg : GEnv) (i : Nat) (l : AllocLabel) : Prop :=
  ∃ c, Eg.sto l = some c ∧ c.owner = some i

/-- The step's fresh labels are empty in `E_g` (the global form of `FreshLP`:
only `g.i` allocates at `freshLabel … g.i …`, S7c). -/
def GFreshE (g : G) (Eg : GEnv) (n n' : Nat) : Prop :=
  ∀ l, FreshIn g n n' l → Eg.sto l = none ∧ Eg.box l = none ∧ Eg.pfr l = none

/-- **A step of thread `g.i` on `E_g`** (from `n` to `n'` allocations, old
`vWr` `v`): the global reading of `EFoot`.  Cells and boxes appear only at the
step's (empty) fresh labels, as `g.i`'s; counts grow, changing only at fresh
labels or `g.i`'s cells; frontiers are set only from none, to at most `v`, at a
cell of `g.i`. -/
def GFoot (g : G) (Eg Eg' : GEnv) (n n' : Nat) (v : Ts) : Prop :=
  Eg'.prog = Eg.prog ∧
  (∀ l, Eg'.sto l = Eg.sto l ∨
    (FreshIn g n n' l ∧ Eg.sto l = none ∧ Eg.pfr l = none ∧ ∃ T, Eg'.sto l = some ⟨T, some g.i⟩)) ∧
  (∀ l, Eg'.box l = Eg.box l ∨
    (FreshIn g n n' l ∧ Eg.box l = none ∧ ∃ B, Eg'.box l = some B ∧ B.own = g.i)) ∧
  (∀ l, Eg.ini l ≤ Eg'.ini l ∧ (Eg'.ini l = Eg.ini l ∨ FreshIn g n n' l ∨ Eg.OwnAt g.i l)) ∧
  (∀ l, Eg'.pfr l = Eg.pfr l ∨
    (Eg.pfr l = none ∧ ∃ f, Eg'.pfr l = some f ∧ f ≤ v ∧ Eg.OwnAt g.i l) ∨
    (FreshIn g n n' l ∧ Eg.pfr l = none ∧ Eg'.sto l = none)) ∧
  (∀ l, Eg.rini l ≤ Eg'.rini l) ∧
  (∀ l, Eg'.rini l = Eg.rini l ∨ FreshIn g n n' l ∨ Eg.OwnAt g.i l)

theorem GFoot_refl {g : G} {Eg : GEnv} {n n' : Nat} {v : Ts} : GFoot g Eg Eg n n' v :=
  ⟨rfl, fun _ => .inl rfl, fun _ => .inl rfl, fun _ => ⟨Nat.le_refl _, .inl rfl⟩, fun _ => .inl rfl,
    fun _ => Nat.le_refl _, fun _ => .inl rfl⟩

open Classical in
/-- **`E_g` after a step of `g.i`** whose S6 witness is `E'`.  (F3) Cells and
boxes merge alike: the step's fresh labels from `E'`, every other label from
`E_g`, so other threads' boxes survive. -/
noncomputable def GEnv.post (Eg : GEnv) (g : G) (n n' : Nat) (E' : TEnv) : GEnv :=
  { prog := Eg.prog, sto := fun l => if FreshIn g n n' l then E'.sto l else Eg.sto l,
    ini := E'.ini, rini := E'.rini, pfr := E'.pfr, box := fun l => if FreshIn g n n' l then E'.box l else Eg.box l,
    fpOf := Eg.fpOf, pubd := fun l => Eg.pubd l ∨ (Eg.pfr l = none ∧ E'.pfr l ≠ none ∧ E'.seen l) }

theorem post_box_fresh {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {l : AllocLabel}
    (h : FreshIn g n n' l) : (Eg.post g n n' E').box l = E'.box l := by
  simp only [GEnv.post, h, ↓reduceIte]

theorem post_box_old {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {l : AllocLabel}
    (h : ¬ FreshIn g n n' l) : (Eg.post g n n' E').box l = Eg.box l := by
  simp only [GEnv.post, h, ↓reduceIte]

theorem post_sto_fresh {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {l : AllocLabel}
    (h : FreshIn g n n' l) : (Eg.post g n n' E').sto l = E'.sto l := by
  simp only [GEnv.post, h, ↓reduceIte]

theorem post_sto_old {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {l : AllocLabel}
    (h : ¬ FreshIn g n n' l) : (Eg.post g n n' E').sto l = Eg.sto l := by
  simp only [GEnv.post, h, ↓reduceIte]

/-- An own cell in the cut is an own cell in `E_g`. -/
theorem OwnAt_cut {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel}
    (h : OwnAt (Cut Eg i S) l) : Eg.OwnAt i l :=
  let ⟨c, hc, ho⟩ := h
  ⟨c, cutSto_sub hc, ho⟩

/-- **S6's footprint on the cut is a global step.** -/
theorem EFoot_post {g : G} {Eg : GEnv} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St}
    (hf : EFoot g (Cut Eg g.i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc)
    (hvz : s.vs.vWr ≤ s.mem.size) :
    GFoot g Eg (Eg.post g s.nalloc s'.nalloc E') s.nalloc s'.nalloc s.mem.size := by
  obtain ⟨_, _, hsto, hbox, hini, hpfr, _, _, _, hri, -, -, hrq, -⟩ := hf
  refine ⟨rfl, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, hri,
    fun l => (hrq l).imp id (Or.imp id OwnAt_cut)⟩
  · by_cases hF : FreshIn g s.nalloc s'.nalloc l
    · rw [post_sto_fresh hF]
      obtain ⟨h0, _, hp0⟩ := hfr l hF
      rcases hsto l with h | ⟨_, T, hT, -⟩
      · left; rw [h, h0]; show cutSto Eg g.i l = none
        cases e : cutSto Eg g.i l with
        | none => rfl
        | some c => rw [cutSto_sub e] at h0; cases h0
      · exact .inr ⟨hF, h0, hp0, T, hT⟩
    · exact .inl (post_sto_old hF)
  · by_cases hF : FreshIn g s.nalloc s'.nalloc l
    · rw [post_box_fresh hF]
      rcases hbox l with h | ⟨-, B, hB, ho, -⟩
      · exact .inl h
      · exact .inr ⟨hF, (hfr l hF).2.1, B, hB, ho⟩
    · exact .inl (post_box_old hF)
  · obtain ⟨h1, h2⟩ := hini l
    exact ⟨h1, h2.imp id (Or.imp id fun h => OwnAt_cut h.1)⟩
  · rcases hpfr l with h | ⟨h1, F, h2, -, hF2, h3, -⟩ | ⟨hF, h0, hs0⟩
    · exact .inl h
    · exact .inr (.inl ⟨h1, F, h2, Nat.le_trans hF2 (Nat.max_le.2 ⟨hvz, Nat.le_refl _⟩), OwnAt_cut h3⟩)
    · exact .inr (.inr ⟨hF, h0, by rw [post_sto_fresh hF]; exact hs0⟩)

/-- **`E_g` grows** along a global step. -/
theorem GFoot.le {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (h : GFoot g Eg Eg' n n' v) : Eg.le Eg' := by
  obtain ⟨hp, hsto, hbox, hini, hpfr, hri, -⟩ := h
  refine ⟨hp, fun l c hc => ?_, fun l => (hini l).1, fun l f hf => ?_, fun l B hB => ?_, hri⟩
  · rcases hsto l with e | ⟨_, e, _⟩
    · rw [e]; exact hc
    · rw [e] at hc; cases hc
  · rcases hpfr l with e | ⟨e, _⟩ | ⟨-, e, -⟩
    · rw [e]; exact hf
    · rw [e] at hf; cases hf
    · rw [e] at hf; cases hf
  · rcases hbox l with e | ⟨_, e, _⟩
    · rw [e]; exact hB
    · rw [e] at hB; cases hB

/-- The cut at `l` is unchanged when the cell is, and its sharing is unchanged
unless it is `i`'s own. -/
theorem cutSto_congr {Eg Eg' : GEnv} {i : Nat} {l : AllocLabel} (hsto : Eg'.sto l = Eg.sto l)
    (hsh : ∀ c, Eg.sto l = some c → c.owner ≠ some i → (Eg'.Shared l ↔ Eg.Shared l)) :
    cutSto Eg' i l = cutSto Eg i l := by
  have key : ∀ c, Eg.sto l = some c → ((c.owner = some i ∨ Eg'.Shared l) ↔ (c.owner = some i ∨ Eg.Shared l)) :=
    fun c hc => by
      by_cases ho : c.owner = some i
      · exact ⟨fun _ => .inl ho, fun _ => .inl ho⟩
      · rw [hsh c hc ho]
  cases e : cutSto Eg i l with
  | none =>
    cases e' : cutSto Eg' i l with
    | none => rfl
    | some c =>
      obtain ⟨h1, h2⟩ := cutSto_some.1 e'
      rw [hsto] at h1
      rw [cutSto_some.2 ⟨h1, (key c h1).1 h2⟩] at e; cases e
  | some c =>
    obtain ⟨h1, h2⟩ := cutSto_some.1 e
    exact cutSto_some.2 ⟨hsto.trans h1, (key c h1).2 h2⟩

/-- **A-strict exactness for the stepping thread**: S6's witness `E'` (its code
view) is exactly the new `E_g`'s cut for `g.i`, with `E'`'s own `seen`. -/
theorem Cut_self {g : G} {Eg : GEnv} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St}
    (hf : EFoot g (Cut Eg g.i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc) :
    CE E' = Cut (Eg.post g s.nalloc s'.nalloc E') g.i E'.seen := by
  have hf' := hf
  obtain ⟨hp, ht, hsto, hbox, _, hpfr, _, _, hfp, -⟩ := hf'
  have hb : E'.box = (Eg.post g s.nalloc s'.nalloc E').box := funext fun l => by
    by_cases hF : FreshIn g s.nalloc s'.nalloc l
    · rw [post_box_fresh hF]
    · rw [post_box_old hF]
      rcases hbox l with h | ⟨h1, _⟩
      · exact h
      · exact absurd h1 hF
  have hs : E'.sto = cutSto (Eg.post g s.nalloc s'.nalloc E') g.i := funext fun l => by
    by_cases hF : FreshIn g s.nalloc s'.nalloc l
    · obtain ⟨h0, _, _⟩ := hfr l hF
      rcases hsto l with h | ⟨_, T, hT, -⟩
      · have hn : cutSto Eg g.i l = none := by
          cases e : cutSto Eg g.i l with
          | none => rfl
          | some c => rw [cutSto_sub e] at h0; cases h0
        have h' : E'.sto l = none := h.trans hn
        rw [h']
        cases e : cutSto (Eg.post g s.nalloc s'.nalloc E') g.i l with
        | none => rfl
        | some c =>
          have := cutSto_sub e
          rw [post_sto_fresh hF, h'] at this; cases this
      · rw [hT]
        exact (cutSto_own (by rw [post_sto_fresh hF]; exact hT) rfl).symm
    · rcases hsto l with h | ⟨h1, _⟩
      · rw [h]
        refine (cutSto_congr (post_sto_old hF) fun c hc ho => ?_).symm
        show (∃ f, E'.pfr l = some f) ↔ (∃ f, Eg.pfr l = some f)
        rcases hpfr l with e | ⟨_, _, _, _, _, ⟨c0, hc0, ho0⟩, -⟩ | ⟨hF', -⟩
        · rw [e]; rfl
        · rw [cutSto_sub hc0] at hc; cases hc; exact absurd ho0 ho
        · exact absurd hF' hF
      · exact absurd h1 hF
  have hp' : E'.prog = Eg.prog := hp
  have ht' : E'.tid = g.i := ht
  have hfp' : E'.fp = Eg.fpOf g.i := hfp
  unfold CE Cut
  rw [hp', hs, ht', hfp', hb]
  rfl

/-- **Other threads' cuts only grow**, by exactly the newly published cell
(`g.i`'s, now with frontier `v`); counts and boxes grow (`Incl`). -/
theorem Cut_other {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (h : GFoot g Eg Eg' n n' v)
    {j : Nat} (hj : j ≠ g.i) (S : AllocLabel → Prop) :
    Incl (Cut Eg j S) (Cut Eg' j S) ∧
    ∀ l c, cutSto Eg' j l = some c → cutSto Eg j l = none →
      Eg.sto l = some c ∧ c.owner = some g.i ∧ Eg.pfr l = none ∧ ∃ f, Eg'.pfr l = some f ∧ f ≤ v := by
  refine ⟨(Cut_le h.le j fun _ h => h).1, fun l c hc hn => ?_⟩
  obtain ⟨_, hsto, _, _, hpfr, -⟩ := h
  obtain ⟨h1, h2⟩ := cutSto_some.1 hc
  rcases hsto l with e | ⟨_, hs0, hp0, T, hT⟩
  · rw [e] at h1
    have hno : ¬ (c.owner = some j ∨ Eg.Shared l) := fun hh => by
      rw [cutSto_some.2 ⟨h1, hh⟩] at hn; cases hn
    rcases hpfr l with ep | ⟨ep0, f0, ep, hfv, ⟨c0, hc0, ho0⟩⟩ | ⟨-, -, hs'⟩
    · rcases h2 with h2 | ⟨f, hf⟩
      · exact absurd (.inl h2) hno
      · rw [ep] at hf; exact absurd (.inr ⟨f, hf⟩) hno
    · rw [hc0] at h1; cases h1
      exact ⟨hc0, ho0, ep0, f0, ep, hfv⟩
    · rw [e, h1] at hs'; cases hs'
  · rw [hT] at h1; cases h1
    rcases h2 with h2 | ⟨f, hf⟩
    · cases h2; exact absurd rfl hj
    · rcases hpfr l with ep | ⟨_, _, _, _, ⟨c0, hc0, _⟩⟩ | ⟨-, -, hs'⟩
      · rw [ep, hp0] at hf; cases hf
      · rw [hs0] at hc0; cases hc0
      · rw [hT] at hs'; cases hs'

/-- Outside the step's fresh labels the store typing is unchanged. -/
theorem GFoot.sto_old {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (h : GFoot g Eg Eg' n n' v)
    {l : AllocLabel} (hl : ¬ FreshIn g n n' l) : Eg'.sto l = Eg.sto l :=
  (h.2.1 l).elim id fun hh => absurd hh.1 hl

/-! ## S7g (1) Uniqueness of a value's resources -/

/-- (S7g) No resourceful relations (`CE`-shaped environments, and everything
`push0`/`unsee` makes of them): a type variable denotes no value with
resources. -/
def NoRR (η : TEnv) : Prop := (∀ k S ws R, ¬ η.rrs k S ws R) ∧ ∀ k S ws R, ¬ η.urrs k S ws R

theorem NoRR.unsee {η : TEnv} (h : NoRR η) : NoRR η.unsee := ⟨h.2, h.2⟩

theorem NoRR.push0 {η : TEnv} (h : NoRR η) (s : Ty) : NoRR (η.push0 s) := by
  constructor
  · intro k S ws R hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk; exact h.1 k S ws R hk
  · intro k S ws R hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk; exact h.2 k S ws R hk

theorem NoRR_CE (η : TEnv) : NoRR (CE η) := ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- (S7g) No resource-carrying component (words, pairs, tokens, shares). -/
def noRes : Ty → Bool
  | .word _ _ | .word2 _ _ | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ => false
  | .prod a b | .sum a b => noRes a && noRes b
  | .refine t _ | .iall t | .iex t | .mu t | .tex _ t => noRes t
  -- (F2′) an own reference carries its own-handle key
  | .ptr .own _ | .loc .own _ | .ptrOpt .own _ => false
  | _ => true

/-- (S7g) A resource-free type's values hold nothing. -/
theorem VRR_noRes : ∀ (t : Ty) {ρ : Nat → Nat} {η : TEnv} {rt : Shp} {ws : List Word} {R : Res},
    NoRR η → noRes t = true → VRR ρ η t rt ws R → R = .zero := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ρ η rt ws R hn ht h
      simp only [noRes, Bool.and_eq_true] at ht
      simp only [VRR] at h
      obtain ⟨ra, rb, -, Ra, Rb, rfl, hz, hab⟩ := h
      cases hw : ra.wc with
      | none => exact hz hw
      | some n =>
          obtain ⟨-, h1, h2⟩ := hab n hw
          rw [iha hn ht.1 h1, ihb hn ht.2 h2]; simp
  | sum a b iha ihb =>
      intro ρ η rt ws R hn ht h
      simp only [noRes, Bool.and_eq_true] at ht
      simp only [VRR] at h
      obtain ⟨n, Ra, Rb, -, h | ⟨j, p, -, h1, h2⟩⟩ := h
      · obtain ⟨-, x, s, B, -, -, -, -, -, -, hL, hR⟩ := h
        by_cases hj : B.tag - s < (armsOf Ra).length
        · obtain ⟨q1, q2⟩ := hL hj
          cases hb : isBoxed Ra
          · obtain ⟨q, -, -, -, -, h5⟩ := q2 hb
            exact iha hn.unsee ht.1 h5
          · exact iha hn ht.1 (q1 hb)
        · obtain ⟨q1, q2⟩ := hR (Nat.le_of_not_lt hj)
          cases hb : isBoxed Rb
          · obtain ⟨q, -, -, -, -, h5⟩ := q2 hb
            exact ihb hn.unsee ht.2 h5
          · exact ihb hn ht.2 (q1 hb)
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, -, h⟩ := h1 hj; exact iha hn ht.1 h
        · obtain ⟨q, -, h⟩ := h2 (Nat.le_of_not_lt hj); exact ihb hn ht.2 h
  | tvar k =>
      intro ρ η rt ws R hn _ h
      simp only [VRR] at h
      obtain ⟨ws', -, h⟩ := h
      exact absurd h (hn.1 _ _ _ _)
  | tex κ b ih =>
      intro ρ η rt ws R hn ht h
      simp only [noRes] at ht
      simp only [VRR] at h
      obtain ⟨n, rb, s, -, -, -, h⟩ := h
      exact ih (hn.push0 s) ht h
  | mu b ih =>
      intro ρ η rt ws R hn ht h
      simp only [noRes] at ht
      simp only [VRR] at h
      exact ih (hn.push0 _) ht h
  | iall b ih =>
      intro ρ η rt ws R hn ht h
      simp only [noRes] at ht
      simp only [VRR] at h
      exact ih hn ht (h 0)
  | iex b ih =>
      intro ρ η rt ws R hn ht h
      simp only [noRes] at ht
      simp only [VRR] at h
      obtain ⟨n, rb, w, -, h⟩ := h
      exact ih hn ht h
  | refine t ψ ih =>
      intro ρ η rt ws R hn ht h
      simp only [noRes] at ht
      simp only [VRR] at h
      exact ih hn ht h.1
  | word _ _ | word2 _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ | share _ =>
      intro ρ η rt ws R _ ht _; simp [noRes] at ht
  | void => intro ρ η rt ws R _ _ h; simp only [VRR] at h
  | unit | array _ _ | cap _ _ => intro ρ η rt ws R _ _ h; simp only [VRR] at h; exact h
  | intS _ | int | opq _ | tid | fix _ _ | lanes _ _ | code _ _ | epair _ _ =>
      intro ρ η rt ws R _ _ h; simp only [VRR] at h; exact h.2
  | ptr μ _ | loc μ _ | ptrOpt μ _ =>
      intro ρ η rt ws R _ ht h; simp only [VRR] at h; rw [h.2]
      cases μ <;> first | rfl | simp [noRes] at ht

theorem wc_array (i : Idx) (e : Ty) : wc (.array i e) = none := rfl

/-- A cell's word count is its type's. -/
theorem CellOKR_len {η η' : TEnv} {n n' nr nr' : Nat} {T : Ty} {v₁ v₂ : List Word} {R₁ R₂ : Res}
    (h1 : CellOKR η n nr T v₁ R₁) (h2 : CellOKR η' n' nr' T v₂ R₂) : v₁.length = v₂.length := by
  rcases h1 with ⟨hw, -⟩ | ⟨N, e, us, Rs, hT1, hu, -, hl, -⟩ <;>
    rcases h2 with ⟨hw', -⟩ | ⟨N', e', us', Rs', hT2, hu', -, hl', -⟩
  · rw [hw] at hw'; exact Option.some.inj hw'
  · rw [hT2, wc_array] at hw; cases hw
  · rw [hT1, wc_array] at hw'; cases hw'
  · rw [hT1] at hT2
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
    obtain ⟨rfl, rfl⟩ := hT2
    rw [hu] at hu'; cases hu'
    rw [hl, hl']

/-- Two word lists of one length, each word at its index determined. -/
theorem vals_eq {v₁ v₂ : List Word} {P : Nat → Word → Prop} (hl : v₁.length = v₂.length)
    (h1 : ∀ o w, v₁[o]? = some w → P o w) (h2 : ∀ o w, v₂[o]? = some w → P o w)
    (hu : ∀ o w w', P o w → P o w' → w = w') : v₁ = v₂ := by
  apply List.ext_getElem? fun o => ?_
  by_cases ho : o < v₁.length
  · have e1 := List.getElem?_eq_getElem ho
    have e2 := List.getElem?_eq_getElem (hl ▸ ho)
    rw [e1, e2, hu o _ _ (h1 o _ e1) (h2 o _ e2)]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem Res.sum_perm {α : Type} {f : α → Res} {L₁ L₂ : List α} (h : L₁.Perm L₂) :
    Res.sum (L₁.map f) = Res.sum (L₂.map f) := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.map_cons, Res.sum_cons, ih]
  | swap x y L =>
      simp only [List.map_cons, Res.sum_cons]
      rw [← Res.add_assoc, ← Res.add_assoc, Res.add_comm (f y) (f x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem Res.sum_filter {α : Type} (p : α → Bool) {f : α → Res} :
    ∀ (L : List α), (∀ x, x ∈ L → p x = false → f x = .zero) →
      Res.sum (L.map f) = Res.sum ((L.filter p).map f)
  | [], _ => rfl
  | x :: L, hz => by
      have ih := Res.sum_filter p L (fun y hy => hz y (List.mem_cons_of_mem _ hy))
      cases hp : p x
      · simp only [List.map_cons, Res.sum_cons, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
        rw [hz x List.mem_cons_self hp, Res.zero_add, ih]
      · simp only [List.map_cons, Res.sum_cons, List.filter_cons, hp, ↓reduceIte, ih]

/-- (S7g) Two sums over duplicate-free lists agree when both lists cover the
support `p`, vanish off it, and the summands agree on it. -/
theorem Res.sum_support {α : Type} [DecidableEq α] (p : α → Bool) {L₁ L₂ : List α} {f g : α → Res}
    (h1 : L₁.Nodup) (h2 : L₂.Nodup) (hp1 : ∀ x, p x = true → x ∈ L₁) (hp2 : ∀ x, p x = true → x ∈ L₂)
    (hz1 : ∀ x, x ∈ L₁ → p x = false → f x = .zero) (hz2 : ∀ x, x ∈ L₂ → p x = false → g x = .zero)
    (hfg : ∀ x, p x = true → f x = g x) : Res.sum (L₁.map f) = Res.sum (L₂.map g) := by
  rw [Res.sum_filter p L₁ hz1, Res.sum_filter p L₂ hz2]
  have hperm : (L₁.filter p).Perm (L₂.filter p) :=
    (List.perm_ext_iff_of_nodup (h1.filter _) (h2.filter _)).2 fun x => by
      simp only [List.mem_filter]
      exact ⟨fun ⟨_, h⟩ => ⟨hp2 x h, h⟩, fun ⟨_, h⟩ => ⟨hp1 x h, h⟩⟩
  rw [List.map_congr_left (fun x hx => hfg x (List.mem_filter.1 hx).2)]
  exact Res.sum_perm hperm

theorem isSome_false {α : Type} {o : Option α} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

/-! ## S7g (2) Splitting memory's holding by label sets -/

/-- (S7g) `MemHeld` restricted to the labels `Q`: a sum over a duplicate-free
list of `Q`-labels covering Σ's `Q`-cells, of each label's entry. -/
def MemHeldOn (Q : AllocLabel → Prop) (E : TEnv) (s : St) (H : Res) : Prop :=
  ∃ (L : List AllocLabel) (Rl : AllocLabel → Res), L.Nodup ∧ (∀ l c, Q l → E.sto l = some c → l ∈ L) ∧
    (∀ l, l ∈ L → Q l) ∧ H = Res.sum (L.map Rl) ∧ ∀ l, l ∈ L → HeldEntry E s l (Rl l)

/-- (S7g) The private part: the thread's own cells without a frontier. -/
def MemHeldP (E : TEnv) (s : St) (H : Res) : Prop := MemHeldOn (Priv E) E s H

/-- (S7g) The shared part: the cells with a frontier (published or planted). -/
def MemHeldS (E : TEnv) (s : St) (H : Res) : Prop := MemHeldOn (fun l => ∃ f, E.pfr l = some f) E s H

/-- (S7g) Split along any label set. -/
theorem MemHeld_splitOn (Q : AllocLabel → Prop) {E : TEnv} {s : St} {H : Res} (h : MemHeld E s H) :
    ∃ H₁ H₂, H = H₁ + H₂ ∧ MemHeldOn Q E s H₁ ∧ MemHeldOn (fun l => ¬ Q l) E s H₂ := by
  classical
  obtain ⟨L, Rl, hn, hc, rfl, he⟩ := h
  refine ⟨Res.sum ((L.filter (fun l => decide (Q l))).map Rl),
    Res.sum ((L.filter (fun l => !decide (Q l))).map Rl), ?_,
    ⟨_, Rl, hn.filter _, fun l c hq hs => List.mem_filter.2 ⟨hc l c hs, by simpa using hq⟩,
      fun l hl => by simpa using (List.mem_filter.1 hl).2, rfl, fun l hl => he l (List.mem_filter.1 hl).1⟩,
    ⟨_, Rl, hn.filter _, fun l c hq hs => List.mem_filter.2 ⟨hc l c hs, by simpa using hq⟩,
      fun l hl => by simpa using (List.mem_filter.1 hl).2, rfl, fun l hl => he l (List.mem_filter.1 hl).1⟩⟩
  rw [← Res.sum_append, ← List.map_append]
  exact Res.sum_perm (List.filter_append_perm _ L).symm

/-- (S7g) Change the label set where the entries off the new one vanish. -/
theorem MemHeldOn_mono {Q Q' : AllocLabel → Prop} {E : TEnv} {s : St} {H : Res} (h : MemHeldOn Q E s H)
    (hq : ∀ l c, Q' l → E.sto l = some c → Q l) (hn : ∀ l c, Q l → ¬ Q' l → E.sto l = some c → False) :
    MemHeldOn Q' E s H := by
  classical
  obtain ⟨L, Rl, hnd, hc, hqL, rfl, he⟩ := h
  refine ⟨L.filter (fun l => decide (Q' l)), Rl, hnd.filter _,
    fun l c hq' hs => List.mem_filter.2 ⟨hc l c (hq l c hq' hs) hs, by simpa using hq'⟩,
    fun l hl => by simpa using (List.mem_filter.1 hl).2, ?_, fun l hl => he l (List.mem_filter.1 hl).1⟩
  refine Res.sum_filter _ L fun l hl hf => (he l hl).1 ?_
  cases e : E.sto l with
  | none => rfl
  | some c => exact (hn l c (hqL l hl) (by simpa using hf) e).elim

/-- (S7g) Join two disjoint label sets covering Σ. -/
theorem MemHeld_joinOn {Q Q' : AllocLabel → Prop} {E : TEnv} {s : St} {H₁ H₂ : Res}
    (h1 : MemHeldOn Q E s H₁) (h2 : MemHeldOn Q' E s H₂) (hdis : ∀ l, Q l → Q' l → False)
    (hcov : ∀ l c, E.sto l = some c → Q l ∨ Q' l) : MemHeld E s (H₁ + H₂) := by
  classical
  obtain ⟨L1, R1, hn1, hc1, hq1, rfl, he1⟩ := h1
  obtain ⟨L2, R2, hn2, hc2, hq2, rfl, he2⟩ := h2
  have hout : ∀ l, l ∈ L2 → l ∉ L1 := fun l h2 h1 => hdis l (hq1 l h1) (hq2 l h2)
  refine ⟨L1 ++ L2, fun l => if l ∈ L1 then R1 l else R2 l, ?_, ?_, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨hn1, hn2, ?_⟩
    intro a ha b hb e
    subst e
    exact hout a hb ha
  · intro l c hs
    rcases hcov l c hs with h | h
    · exact List.mem_append_left _ (hc1 l c h hs)
    · exact List.mem_append_right _ (hc2 l c h hs)
  · rw [List.map_append, Res.sum_append]
    congr 1
    · exact congrArg Res.sum (List.map_congr_left fun l hl => by simp [hl])
    · exact congrArg Res.sum (List.map_congr_left fun l hl => by simp [hout l hl])
  · intro l hl
    rcases List.mem_append.1 hl with h | h
    · have := he1 l h; simp only [h, ↓reduceIte]; exact this
    · have := he2 l h; simp only [hout l h, ↓reduceIte]; exact this

/-- **(S7g) `MemHeld_split`**: where every non-private cell has a frontier (as
in a cut, `Cut_cov`), memory's holding is its private part plus its shared
part. -/
theorem MemHeld_split {E : TEnv} {s : St} {H : Res}
    (hcov : ∀ l c, E.sto l = some c → ¬ Priv E l → ∃ f, E.pfr l = some f) (h : MemHeld E s H) :
    ∃ HP HS, H = HP + HS ∧ MemHeldP E s HP ∧ MemHeldS E s HS := by
  obtain ⟨H1, H2, rfl, h1, h2⟩ := MemHeld_splitOn (Priv E) h
  refine ⟨H1, H2, rfl, h1, MemHeldOn_mono h2 (fun l c ⟨f, hf⟩ _ => fun hp => ?_)
    (fun l c hp hn hs => hn (hcov l c hs hp))⟩
  rw [hp.2] at hf; cases hf

/-- **(S7g) `MemHeld_join`**: the private and the shared parts recompose. -/
theorem MemHeld_join {E : TEnv} {s : St} {HP HS : Res}
    (hcov : ∀ l c, E.sto l = some c → ¬ Priv E l → ∃ f, E.pfr l = some f)
    (hp : MemHeldP E s HP) (hs : MemHeldS E s HS) : MemHeld E s (HP + HS) :=
  MemHeld_joinOn hp hs (fun l hp ⟨f, hf⟩ => by rw [hp.2] at hf; cases hf)
    (fun l c h => (Classical.em (Priv E l)).imp id (hcov l c h))

/-- (S7g) In a cut, every non-private cell is shared. -/
theorem Cut_cov {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell}
    (h : (Cut Eg i S).sto l = some c) (hp : ¬ Priv (Cut Eg i S) l) : ∃ f, (Cut Eg i S).pfr l = some f := by
  obtain ⟨h1, h2⟩ := cutSto_some.1 h
  rcases h2 with h2 | h2
  · cases e : Eg.pfr l with
    | none => exact (hp ⟨⟨c, h, h2⟩, e⟩).elim
    | some f => exact ⟨f, e⟩
  · exact h2

/-! ## S7g (3) Resources at word units (`ResWU`) -/

/-- (S7g) Offset `o` of a cell of type `T` is a word unit (`WordUnit`'s
disjunction): a non-ghost protocol word, or either word of a protocol pair. -/
def WUOff (T : Ty) (o : Nat) : Prop :=
  (∃ r P, P.ghost = false ∧ AtOff T o (.word r P)) ∨ (∃ r P, AtOff T o (.word2 r P)) ∨
    (∃ r P, 1 ≤ o ∧ AtOff T (o - 1) (.word2 r P))

theorem WordUnit_iff {E : TEnv} {a : Address} :
    WordUnit E a ↔ ∃ c, E.sto a.label = some c ∧ WUOff c.ty a.offset := Iff.rfl

theorem WUOff_fst {a b : Ty} {o : Nat} (h : WUOff a o) : WUOff (.prod a b) o := by
  rcases h with ⟨r, P, hg, h⟩ | ⟨r, P, h⟩ | ⟨r, P, h1, h⟩
  · exact Or.inl ⟨r, P, hg, .fst h⟩
  · exact Or.inr (Or.inl ⟨r, P, .fst h⟩)
  · exact Or.inr (Or.inr ⟨r, P, h1, .fst h⟩)

theorem WUOff_snd {a b : Ty} {us : List Acc} {o : Nat} (hu : accs a = some us) (h : WUOff b o) :
    WUOff (.prod a b) (nWords us + o) := by
  rcases h with ⟨r, P, hg, h⟩ | ⟨r, P, h⟩ | ⟨r, P, h1, h⟩
  · exact Or.inl ⟨r, P, hg, .snd hu h⟩
  · exact Or.inr (Or.inl ⟨r, P, .snd hu h⟩)
  · refine Or.inr (Or.inr ⟨r, P, by omega, ?_⟩)
    rw [show nWords us + o - 1 = nWords us + (o - 1) by omega]
    exact .snd hu h

theorem WUOff_elem {e : Ty} {us : List Acc} {n j o : Nat} (hu : accs e = some us) (hj : j < n)
    (h : WUOff e o) : WUOff (.array (.lit n) e) (j * nWords us + o) := by
  rcases h with ⟨r, P, hg, h⟩ | ⟨r, P, h⟩ | ⟨r, P, h1, h⟩
  · exact Or.inl ⟨r, P, hg, .elem hu hj h⟩
  · exact Or.inr (Or.inl ⟨r, P, .elem hu hj h⟩)
  · refine Or.inr (Or.inr ⟨r, P, by omega, ?_⟩)
    rw [show j * nWords us + o - 1 = j * nWords us + (o - 1) by omega]
    exact .elem hu hj h

theorem list_eq_of_agree {ws ws' : List Word} (hl : ws.length = ws'.length)
    (h : ∀ o, o < ws.length → ws[o]? = ws'[o]?) : ws = ws' := by
  apply List.ext_getElem? fun o => ?_
  by_cases ho : o < ws.length
  · exact h o ho
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## S7g (4) The global shared holding (`MemHeldG`) and cut-invariance -/

/-- (S7g) Every thread's promises. -/
def allProms (c : Cfg) : List Ts := c.ths.toList.flatMap (·.promises)

/-- (S7g) A word unit of `E_g`'s cell at `a` (`WordUnit`, globally). -/
def WordUnitG (Eg : GEnv) (a : Address) : Prop := ∃ c, Eg.sto a.label = some c ∧ WUOff c.ty a.offset

/-- (U3) `IniW` read off `E_g`. -/
def IniWG (Eg : GEnv) (a : Address) : Prop :=
  ∀ c N e us, Eg.sto a.label = some c → c.ty = .array (.lit N) e → accs e = some us →
    a.offset < Eg.ini a.label * nWords us

/-- (U3) `IniWr` read off `E_g`: at the real count `min ini rini` (`TEnv.rc`). -/
def IniWrG (Eg : GEnv) (a : Address) : Prop :=
  ∀ c N e us, Eg.sto a.label = some c → c.ty = .array (.lit N) e → accs e = some us →
    a.offset < min (Eg.ini a.label) (Eg.rini a.label) * nWords us

/-- (U3) A predicted unit, read off `E_g` (`PredU`; at a
shared label the two agree, `PredU_cut_shared`). -/
def PredUG (Eg : GEnv) (a : Address) : Prop := IniWG Eg a ∧ ¬ IniWrG Eg a

open Classical in
/-- (S7g) The promises skipped when reading shared memory at `a`: none at a
word unit (it is read promises included, `PromAt_word`), every thread's
otherwise (the latest message that is nobody's promise); (U3) at a predicted
unit only those above the first write (`AboveFW`). -/
noncomputable def PromAtG (Eg : GEnv) (c : Cfg) (a : Address) : List Ts :=
  if WordUnitG Eg a then []
  else if PredUG Eg a then (allProms c).filter (fun t => decide (AboveFW c.mem a t))
  else allProms c

theorem PromAtG_word {Eg : GEnv} {c : Cfg} {a : Address} (h : WordUnitG Eg a) : PromAtG Eg c a = [] := by
  simp [PromAtG, h]

open Classical in
/-- (S7g) `E_g`'s published part as a thread-free environment: the shared
cells only. -/
noncomputable def PubE (Eg : GEnv) : TEnv :=
  { prog := Eg.prog, sto := fun l => if Eg.Shared l then Eg.sto l else none, ini := Eg.ini, rini := Eg.rini, pfr := Eg.pfr,
    box := Eg.box }

theorem PubE_sto {Eg : GEnv} {l : AllocLabel} (h : Eg.Shared l) : (PubE Eg).sto l = Eg.sto l := by
  simp [PubE, h]

/-- (S7g) Every cut's shared part is in `PubE`. -/
theorem InclS_cut_pub (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : InclS (Cut Eg i S) (PubE Eg) :=
  ⟨rfl, fun l c f hc hf => by rw [PubE_sto ⟨f, hf⟩]; exact cutSto_sub hc, fun _ => Nat.le_refl _,
    fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

/-- (S7g) A shared cell reads the same in every cut. -/
theorem cutSto_eq_shared {Eg : GEnv} {i : Nat} {l : AllocLabel} (h : Eg.Shared l) : cutSto Eg i l = Eg.sto l := by
  cases e : Eg.sto l with
  | none =>
      cases e2 : cutSto Eg i l with
      | none => rfl
      | some c => rw [cutSto_sub e2] at e; cases e
  | some c => exact cutSto_shared e h

/-- **(S7g) `MemHeldG`**: the global shared holding — over `E_g`'s shared
cells, each cell's words the latest messages that are nobody's promise (word
units: promises included), typed in `PubE`. -/
def MemHeldG (Eg : GEnv) (c : Cfg) (HS : Res) : Prop :=
  ∃ (L : List AllocLabel) (Rl : AllocLabel → Res), L.Nodup ∧
    (∀ l cl, Eg.Shared l → Eg.sto l = some cl → l ∈ L) ∧ (∀ l, l ∈ L → Eg.Shared l) ∧
    HS = Res.sum (L.map Rl) ∧
    ∀ l, l ∈ L → (Eg.sto l = none → Rl l = .zero) ∧
      ∀ cl, Eg.sto l = some cl → ∃ vals,
        (∀ o w, vals[o]? = some w → LatestNP c.mem (PromAtG Eg c ⟨l, o⟩) ⟨l, o⟩ w) ∧
        CellOKR (PubE Eg) (Eg.ini l) ((PubE Eg).rc l) cl.ty vals (Rl l)

/-! ## S7i (c2) The shared holding across cuts, uniqueness-free

Thread `i`'s cut skips its own promises and
its foreign ones (`fp := Eg.fpOf i`) at the non-word units of shared cells, so
when that list is, as a set, every promise of the configuration (`PromsOK`),
the cut reads every shared cell exactly as the global reading `MemHeldG` does.
Resources are not determined by the words (no `ResRigid`/`WuR`), so the shared
holding is not unique; instead the witness is chosen once, globally
(`MemHeldG`), and every cut adopts it (`MemHeldS_of_G`) or provides it
(`MemHeldG_of_S`). -/

/-- (S7i) **The ghost foreign promises are the system's**: for every thread
`i`, its own promises together with `Eg.fpOf i` are, as a set, every promise of
the configuration. -/
def PromsOK (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ i th, c.ths[i]? = some th → ∀ t, t ∈ th.promises ++ Eg.fpOf i ↔ t ∈ allProms c

theorem PromAtG_nword {Eg : GEnv} {c : Cfg} {a : Address} (h : ¬ WordUnitG Eg a) (hq : ¬ PredUG Eg a) :
    PromAtG Eg c a = allProms c := by
  simp [PromAtG, h, hq]

open Classical in
/-- (U3) Membership at a predicted unit, globally. -/
theorem mem_PromAtG_pred {Eg : GEnv} {c : Cfg} {a : Address} {t : Ts} (h : ¬ WordUnitG Eg a) (hq : PredUG Eg a) :
    t ∈ PromAtG Eg c a ↔ t ∈ allProms c ∧ AboveFW c.mem a t := by
  simp only [PromAtG, h, hq, ↓reduceIte, List.mem_filter, decide_eq_true_eq]

/-- (S7i) `PubE`'s shared part is in every cut. -/
theorem InclS_pub_cut (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : InclS (PubE Eg) (Cut Eg i S) :=
  ⟨rfl, fun l c f hc hf => by rw [PubE_sto ⟨f, hf⟩] at hc; exact cutSto_shared hc ⟨f, hf⟩,
    fun _ => Nat.le_refl _, fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

/-- (S7i) A word unit of a shared cell in a cut is a global one. -/
theorem WordUnit_cut_shared {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel} {o : Nat}
    (hs : Eg.Shared l) : WordUnit (Cut Eg i S) ⟨l, o⟩ ↔ WordUnitG Eg ⟨l, o⟩ := by
  rw [WordUnit_iff]
  show (∃ c, cutSto Eg i l = some c ∧ WUOff c.ty o) ↔ ∃ c, Eg.sto l = some c ∧ WUOff c.ty o
  rw [cutSto_eq_shared hs]

/-- (U3) At a shared label, a cut's predicted units are the global ones. -/
theorem PredU_cut_shared {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel} {o : Nat}
    (hs : Eg.Shared l) : PredU (Cut Eg i S) ⟨l, o⟩ ↔ PredUG Eg ⟨l, o⟩ := by
  obtain ⟨f, hf⟩ := hs
  have hV : (Cut Eg i S).pfr l ≠ none := fun h => by
    have h' : Eg.pfr l = none := h
    rw [hf] at h'; cases h'
  have he : (Cut Eg i S).sto l = Eg.sto l := cutSto_eq_shared ⟨f, hf⟩
  show ((Cut Eg i S).pfr l ≠ none ∧
      (∀ c N e us, (Cut Eg i S).sto l = some c → c.ty = .array (.lit N) e → accs e = some us →
        o < (Cut Eg i S).ini l * nWords us) ∧
      ¬ (∀ c N e us, (Cut Eg i S).sto l = some c → c.ty = .array (.lit N) e → accs e = some us →
        o < (Cut Eg i S).rc l * nWords us)) ↔
    ((∀ c N e us, Eg.sto l = some c → c.ty = .array (.lit N) e → accs e = some us → o < Eg.ini l * nWords us) ∧
      ¬ (∀ c N e us, Eg.sto l = some c → c.ty = .array (.lit N) e → accs e = some us →
        o < min (Eg.ini l) (Eg.rini l) * nWords us))
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hV, h⟩⟩

/-- **(S7i) Reading agreement**: at a shared cell, a cut whose skipped
promises are the system's (`hP`) reads memory as the global reading. -/
theorem latest_cut_G {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {s : St} {c : Cfg} {l : AllocLabel}
    {o : Nat} {w : Word} (hs : Eg.Shared l) (hmem : s.mem = c.mem)
    (hP : ∀ t, t ∈ s.promises ++ Eg.fpOf i ↔ t ∈ allProms c) :
    LatestNP s.mem (PromAt (Cut Eg i S) s ⟨l, o⟩) ⟨l, o⟩ w ↔ LatestNP c.mem (PromAtG Eg c ⟨l, o⟩) ⟨l, o⟩ w := by
  obtain ⟨f, hf⟩ := hs
  have hV : Vis (Cut Eg i S) l := Vis_pfr (E := Cut Eg i S) hf
  rw [hmem]
  by_cases hw : WordUnitG Eg ⟨l, o⟩
  · rw [PromAt_word ⟨(WordUnit_cut_shared ⟨f, hf⟩).2 hw, hV⟩, PromAtG_word hw]
  · have hnv : ¬ VisU (Cut Eg i S) ⟨l, o⟩ := fun h => hw ((WordUnit_cut_shared ⟨f, hf⟩).1 h.1)
    by_cases hq : PredUG Eg ⟨l, o⟩
    · have hq' : PredU (Cut Eg i S) ⟨l, o⟩ := (PredU_cut_shared ⟨f, hf⟩).2 hq
      constructor
      · exact LatestNP_congrP fun t _ _ _ => by
          rw [mem_PromAt_pred hnv hq', mem_PromAtG_pred hw hq, FpAt_vis (a := ⟨l, o⟩) hV, Cut_fp, hP t, hmem]
      · exact LatestNP_congrP fun t _ _ _ => by
          rw [mem_PromAt_pred hnv hq', mem_PromAtG_pred hw hq, FpAt_vis (a := ⟨l, o⟩) hV, Cut_fp, hP t, hmem]
    rw [PromAt_nword hnv (fun h => hq ((PredU_cut_shared ⟨f, hf⟩).1 h)), FpAt_vis (a := ⟨l, o⟩) hV,
      PromAtG_nword hw hq, Cut_fp]
    exact ⟨LatestNP_congrP fun t _ _ _ => hP t, LatestNP_congrP fun t _ _ _ => (hP t).symm⟩

/-- **(S7i) `MemHeldS_of_G`, recomposition**: the global shared holding is a
shared part of every cut whose skipped promises are the system's (shared cell
types `noOR`). -/
theorem MemHeldS_of_G {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {s : St} {c : Cfg} {HS : Res}
    (hmem : s.mem = c.mem) (hT : ∀ l cl, Eg.Shared l → Eg.sto l = some cl → noOR cl.ty = true)
    (hP : ∀ t, t ∈ s.promises ++ Eg.fpOf i ↔ t ∈ allProms c)
    (hg : MemHeldG Eg c HS) : MemHeldS (Cut Eg i S) s HS := by
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := hg
  refine ⟨L, Rl, hn, fun l cl hs hcl => hc l cl hs (cutSto_sub hcl), hq, rfl, fun l hl => ⟨fun h0 => ?_,
    fun cl hcl => ?_⟩⟩
  · exact (he l hl).1 (by rw [← cutSto_eq_shared (hq l hl)]; exact h0)
  · have hcl' : Eg.sto l = some cl := cutSto_sub hcl
    obtain ⟨vals, hv, hk⟩ := (he l hl).2 cl hcl'
    exact ⟨vals, fun o w h => (latest_cut_G (hq l hl) hmem hP).2 (hv o w h),
      CellOKR_transferS (InclS_pub_cut Eg i S) (hT l cl (hq l hl) hcl') hk⟩

/-- **(S7i) `MemHeldG_of_S`, from the stepper**: a cut's shared part, with its
skipped promises the system's, is a global shared holding. -/
theorem MemHeldG_of_S {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {s : St} {c : Cfg} {HS : Res}
    (hmem : s.mem = c.mem) (hT : ∀ l cl, Eg.Shared l → Eg.sto l = some cl → noOR cl.ty = true)
    (hP : ∀ t, t ∈ s.promises ++ Eg.fpOf i ↔ t ∈ allProms c)
    (h : MemHeldS (Cut Eg i S) s HS) : MemHeldG Eg c HS := by
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := h
  refine ⟨L, Rl, hn, fun l cl hs hcl => hc l cl hs (cutSto_shared hcl hs), hq, rfl, fun l hl => ⟨fun h0 => ?_,
    fun cl hcl => ?_⟩⟩
  · exact (he l hl).1 (show cutSto Eg i l = none by rw [cutSto_eq_shared (hq l hl)]; exact h0)
  · obtain ⟨vals, hv, hk⟩ := (he l hl).2 cl (cutSto_shared hcl (hq l hl))
    exact ⟨vals, fun o w h => (latest_cut_G (hq l hl) hmem hP).1 (hv o w h),
      CellOKR_transferS (InclS_cut_pub Eg i S) (hT l cl (hq l hl) hcl) hk⟩

/-- **(S7i) `HeldEntry_cut`**: a shared cell's entry moves between two cuts
whose skipped promises are both the system's. -/
theorem HeldEntry_cut {Eg : GEnv} {i j : Nat} {S S' : AllocLabel → Prop} {s s' : St} {c : Cfg}
    {l : AllocLabel} {R : Res} (hsh : Eg.Shared l)
    (hT : ∀ cl, Eg.sto l = some cl → noOR cl.ty = true) (hm : s.mem = c.mem) (hm' : s'.mem = c.mem)
    (hP : ∀ t, t ∈ s.promises ++ Eg.fpOf i ↔ t ∈ allProms c)
    (hP' : ∀ t, t ∈ s'.promises ++ Eg.fpOf j ↔ t ∈ allProms c)
    (h : HeldEntry (Cut Eg i S) s l R) : HeldEntry (Cut Eg j S') s' l R := by
  have e : ∀ k (T : AllocLabel → Prop), (Cut Eg k T).sto l = Eg.sto l := fun k T => cutSto_eq_shared hsh
  refine ⟨fun h0 => h.1 (by rw [e]; rw [e] at h0; exact h0), fun cl hcl => ?_⟩
  obtain ⟨vals, hv, hk⟩ := h.2 cl (by rw [e]; rw [e] at hcl; exact hcl)
  exact ⟨vals, fun o w hw => (latest_cut_G hsh hm' hP').2 ((latest_cut_G hsh hm hP).1 (hv o w hw)),
    CellOKR_cut (hT cl (by rw [e] at hcl; exact hcl)) hk⟩

/-- (S7g) A shared word unit's resources read the same in every cut. -/
theorem VRes_cut_shared {Eg : GEnv} {i j : Nat} {S S' : AllocLabel → Prop} {a : Address} {w : Word} {R : Res}
    (h : Eg.Shared a.label) : VRes (Cut Eg i S) a w R ↔ VRes (Cut Eg j S') a w R := by
  obtain ⟨f, hf⟩ := h
  have hs : (Cut Eg j S').sto a.label = (Cut Eg i S).sto a.label :=
    (cutSto_eq_shared ⟨f, hf⟩).trans (cutSto_eq_shared ⟨f, hf⟩).symm
  have hI := IniW_congr (E := Cut Eg i S) (E' := Cut Eg j S') (a := a) hs rfl
  have hV1 : Vis (Cut Eg i S) a.label := Vis_pfr (E := Cut Eg i S) hf
  have hV2 : Vis (Cut Eg j S') a.label := Vis_pfr (E := Cut Eg j S') hf
  unfold VRes
  rw [hI, WRes_congr (E := Cut Eg i S) (E' := Cut Eg j S') hs]
  simp only [hV1, hV2, true_and]

/-! ## S7g (5) Closed cell types (`StoClo`) -/

/-- (S7g) `E_g`'s cell types are closed. -/
def GStoClo (Eg : GEnv) : Prop := ∀ l c, Eg.sto l = some c → Clo c.ty

theorem StoClo_Cut {Eg : GEnv} (h : GStoClo Eg) (i : Nat) (S : AllocLabel → Prop) :
    TermTyped.StoClo (Cut Eg i S) := fun l c hc => h l c (cutSto_sub hc)

theorem StoClo_PubE {Eg : GEnv} (h : GStoClo Eg) : TermTyped.StoClo (PubE Eg) := fun l c hc => by
  by_cases hs : Eg.Shared l
  · rw [PubE_sto hs] at hc; exact h l c hc
  · simp [PubE, hs] at hc

/-- (S7g) Initially (no cells) `GStoClo` holds. -/
theorem GStoClo_empty : GStoClo {} := fun _ _ h => by cases h

/-- (U3) **Box payloads name allocated labels**: every reference
word of every box of `E_g` names a label with a cell or a box in `E_g`.  A
`SysInvW` clause; its thread-step preservation is open (tvar-typed
boxing). -/
def GBoxNamed (Eg : GEnv) : Prop :=
  ∀ l B, Eg.box l = some B → ∀ w ∈ B.pay, ∀ (a : Address) (g : Nat), w.val = .loc a g →
    (∃ c, Eg.sto a.label = some c) ∨ ∃ B', Eg.box a.label = some B'

/-- (U3 R1) At a cut every box is `E_g`'s, so its payload names labels
allocated in `E_g`. -/
theorem BoxNamed_cut {Eg : GEnv} (h : GBoxNamed Eg) {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel}
    {B : Box} (hB : (Cut Eg i S).box l = some B) {w : Word} (hw : w ∈ B.pay) {a : Address} {g : Nat}
    (e : w.val = .loc a g) : (∃ c, Eg.sto a.label = some c) ∨ ∃ B', Eg.box a.label = some B' :=
  h l B hB w hw a g e

/-- (U3 R1) Initially (no boxes) `GBoxNamed` holds. -/
theorem GBoxNamed_empty : GBoxNamed {} := fun _ _ h => by cases h

#print axioms noOR_ptr
#print axioms noOR_ptrOpt
#print axioms noOR_loc
#print axioms ModeOK_pub_pfr
#print axioms ModeOK_pub_move
#print axioms VR_transferS
#print axioms VRR_transferS
#print axioms noOR_of
#print axioms InclS.of_incl
#print axioms InclS.refl
#print axioms InclS.trans
#print axioms noOR_seg
#print axioms noOR_array
#print axioms ValOf_transferS
#print axioms ValOfS_transferS
#print axioms WordOK_transferS
#print axioms PairOK_transferS
#print axioms BufOK_transferS
#print axioms CellOK_transferS
#print axioms ValOfR_transferS
#print axioms BufOKR_transferS
#print axioms CellOKR_transferS
#print axioms EnvVal_transferS
#print axioms GEnv.le.refl
#print axioms GEnv.le.trans
#print axioms Cut_sto
#print axioms CE_Cut
#print axioms cutSto_some
#print axioms cutSto_own
#print axioms cutSto_shared
#print axioms cutSto_priv
#print axioms cutSto_sub
#print axioms InclS_cut
#print axioms Cut_le
#print axioms WordOK_cut
#print axioms CellOKR_cut
#print axioms InclS_cert_cut
#print axioms GFoot_refl
#print axioms post_sto_fresh
#print axioms post_sto_old
#print axioms OwnAt_cut
#print axioms EFoot_post
#print axioms GFoot.le
#print axioms cutSto_congr
#print axioms Cut_self
#print axioms Cut_other
#print axioms GFoot.sto_old
#print axioms CellOKR_len
#print axioms MemHeld_splitOn
#print axioms MemHeld_joinOn
#print axioms MemHeldOn_mono
#print axioms MemHeld_split
#print axioms MemHeld_join
#print axioms Cut_cov
#print axioms InclS_cut_pub
#print axioms cutSto_eq_shared
#print axioms Cut_fp
#print axioms Cut_rini
#print axioms TEnv.selIni_le_one
#print axioms PromAtG_nword
#print axioms mem_PromAtG_pred
#print axioms PredU_cut_shared
#print axioms InclS_pub_cut
#print axioms WordUnit_cut_shared
#print axioms latest_cut_G
#print axioms MemHeldS_of_G
#print axioms MemHeldG_of_S
#print axioms HeldEntry_cut
#print axioms VRes_cut_shared
#print axioms StoClo_Cut
#print axioms StoClo_PubE
#print axioms GStoClo_empty
#print axioms BoxNamed_cut
#print axioms GBoxNamed_empty
#print axioms post_box_fresh
#print axioms post_box_old
#print axioms LabIn_take
#print axioms LabIn_drop
#print axioms LabIn_one
#print axioms LabIn_nil
#print axioms LabIn_cst
#print axioms LabIn_retag
#print axioms LabIn_encodeArm
#print axioms LabIn_ofArm
#print axioms LabIn_decodeArm
#print axioms IniR_monoL
#print axioms ModeOK_pub_moveL
#print axioms VR_transferL
#print axioms SegOf_accs
#print axioms LabIn_of_get
#print axioms Bnd_cons
#print axioms Bnd_oneAt
#print axioms Bnd_embed
#print axioms Bnd_atOff_oneAt
#print axioms wordOK_back

end TermCut
