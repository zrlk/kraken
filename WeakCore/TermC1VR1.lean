import WeakCore.TermC1Inv
import WeakCore.TermMem

/-! `VR1` = `VR` (TermSound:1412-1480) with `ModeOK` → `ModeOK1` (TermC1Inv:26-30: a
region reference held to the `pub` clause), and its `up` / `mono` / `unsee` lemmas, copied arm for arm from
`VR_up` (TermSound:1776), `VR_mono` (:2368) and `VR_unsee` (:2608); the `ModeOK1` `rgn` arms repeat the `pub`
proofs.  `EnvVal1.store` is `EnvVal.store` (TermMem:69-77) over `VR1`, taking `SeenLE` (TermMem:49) verbatim:
a relaxed store's message view is ≥ vRelSt (Promises:394-395), so a seen region cell's frontier is below it.
pfr/seen at `region` / `intoRgn` are already published by TermC1Rgn (`pubStep1` :131, `ModeOK1_rgn_seen` :149,
`tstepM_region1` :160, `tstepM_intoRgn1` :238), not rebuilt here. -/
namespace TermC1
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `VR` with `ModeOK1`: a region reference's cell is published and seen or below the word's view. -/
def VR1 (ρ : Nat → Nat) (η : TEnv) : Ty → Shp → List Word → Prop
  | .intS i, _, ws => ws.map (·.val) = [.num (ev ρ i)]
  | .int, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | .opq _, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | .tid, _, ws => ∃ l c, ws.map (·.val) = [.loc ⟨l, 0⟩ 0] ∧ η.sto l = some c ∧ c.ty = .unit ∧
      ModeOK1 η.tid η.pfr η.seen .pub l c ws
  | .fix sg w, rt, ws => rt = .fix sg w ∧ ∃ n, ws.map (·.val) = [.num n] ∧ n < pw2 w
  | .lanes sg w, rt, ws => rt = .lanes sg w ∧ ∃ n, ws.map (·.val) = [.num n]
  | .refine t ψ, rt, ws => VR1 ρ η t rt ws ∧ IniR ρ (η.selIni t) ψ ws
  | .iex b, rt, ws => ∃ n rb w, rt = .iex n rb ∧ VR1 (vcons w ρ) η b rb ws
  | .prod a b, rt, ws => ∃ ra rb, rt = .prod ra rb ∧ ∀ n, ra.wc = some n →
      n ≤ ws.length ∧ VR1 ρ η a ra (ws.take n) ∧ VR1 ρ η b rb (ws.drop n)
  -- T3c-5d: a boxed sum is a reference to a box whose payload, re-injected into
  -- the summand its tag (less the offset `s`) selects, is a value there; a boxed
  -- summand is read through the same reference, its tag offset further (`vsh`)
  | .sum a b, rt, ws => ∃ n Ra Rb, rt = .sum n (.sum Ra Rb) ∧
      (((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x s B, ws.map (·.val) = [.loc x 0] ∧ x.offset = 0 ∧
          η.box x.label = some B ∧ n = some (s + 1) ∧
          (s ≤ B.tag ∧ ((armsOf (.sum Ra Rb))[B.tag - s]?).bind wc = some B.pay.length) ∧
          ((η.seen x.label ∧ ∃ f, η.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) ∧
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VR1 ρ η a (vsh s (shp Ra)) ws) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) B.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VR1 ρ η.unsee a (shp Ra) q)) ∧
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VR1 ρ η b (vsh (s + (armsOf Ra).length) (shp Rb)) ws) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VR1 ρ η.unsee b (shp Rb) q))) ∨ ∃ j p,
        decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws = some (j, p) ∧
        (j < (armsOf Ra).length → ∃ q, ofArm Ra j p = some q ∧ VR1 ρ η a (shp Ra) q) ∧
        ((armsOf Ra).length ≤ j → ∃ q, ofArm Rb (j - (armsOf Ra).length) p = some q ∧ VR1 ρ η b (shp Rb) q))
  | .tvar k, rt, ws => ∃ ws', WLe ws' ws ∧ η.get k rt ws'
  | .code σ τ _, rt, ws => ∃ i d, ws.map (·.val) = [.num i] ∧ η.prog[i]? = some d ∧
      η.prog.find? (·.name == d.name) = some d ∧ d.tparams = [] ∧ d.idx = [] ∧
      cl ρ η.wit 0 0 σ = clD d.argTy ∧ cl ρ η.wit 0 0 τ = clD d.retTy
  -- T3c-3: a reference's cell is in Σ, holds exactly the closure of the target
  -- type (invariant: no strong update), and agrees with the mode
  | .ptr μ u, _, ws => ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
      Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOK1 η.tid η.pfr η.seen μ a.label c ws ∧ accs c.ty ≠ none
  -- F5: `null` is a locative only to a zero-length array (`zeroableIn`), which
  -- no access reaches (T3c-5a)
  | .loc μ u, _, ws => (ws.map (·.val) = [.null] ∧ ∃ e, Fd (.array (.lit 0) e) (cl ρ η.wit 0 0 u)) ∨
      ∃ a c U, ws.map (·.val) = [.loc a 0] ∧ η.sto a.label = some c ∧
        AtOff c.ty a.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ ModeOK1 η.tid η.pfr η.seen μ a.label c ws ∧
          IniAt (modeIni μ η.ini η.rini) c a U
  | .ptrOpt μ u, _, ws => ws.map (·.val) = [.null] ∨
      ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
        Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOK1 η.tid η.pfr η.seen μ a.label c ws ∧ accs c.ty ≠ none
  | .void, _, _ => False
  -- T3c: some closed witness `s`; its variable has no values (`push0`), which
  -- `guardT` keeps where `VR1` reads only witnesses (code signatures, and from
  -- T3c-3 reference targets)
  | .tex κ b, rt, ws => ∃ n rb s, rt = .tex n rb ∧ Clo s ∧ WitOK κ s ∧ VR1 ρ (η.push0 s) b rb ws
  -- T3c-5a (notes §2a): the body, its variable the closed `μ` type itself; the
  -- variable is guarded (`guardT`), so its (empty, `push0`) relation is never
  -- read, and `VR1` at a reference to it compares with the witness
  | .mu b, rt, ws => VR1 ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) b rt ws
  -- T3c-5f: indices are erased, so a value of `∀i. b` is, on the same words, a
  -- value of `b` at every index
  | .iall b, rt, ws => ∀ n, VR1 (vcons n ρ) η b rt ws
  -- T3d-1: a protocol word's protocol is well formed (`mkWord` checks it), and a
  -- runtime word holds a state of it
  | .word _ P, _, ws => pwf P = true ∧ (P.ghost = false → ∃ n, ws.map (·.val) = [.num n] ∧ InP P n)
  -- T3d-1: a protocol pair holds a pair state (`mkWord2`, `stp` and `casp`
  -- check one); an epoch pair holds two numbers (`caspE` writes the live
  -- token's epoch and an arbitrary value, so nothing stronger is invariant)
  | .word2 _ P, _, ws => pwf2 P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] ∧ InP2 P n0 n1
  | .epair _ P, _, ws => pwfE P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1]
  | _, _, _ => True

theorem ModeOK1_mono {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} (hP : ∀ l f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws ws' : List Word}
    (hw : ∀ f, (∀ w ∈ ws, f ≤ w.view) → ∀ w ∈ ws', f ≤ w.view) :
    ModeOK1 i P S μ l c ws → ModeOK1 i P' S' μ l c ws' := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2⟩
    · exact ⟨f, hP l f h1, Or.inl (hS l h2)⟩
    · exact ⟨f, hP l f h1, Or.inr (hw f h2)⟩
  | rgn _ =>
    rintro ⟨f, h1, h2 | h2⟩
    · exact ⟨f, hP l f h1, Or.inl (hS l h2)⟩
    · exact ⟨f, hP l f h1, Or.inr (hw f h2)⟩

/-- `ModeOK_unsee` for `ModeOK1`; the `rgn` arm is the `pub` proof. -/
theorem ModeOK1_unsee {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} {V : WeakMem.Ts}
    (hP : ∀ l f, P l = some f → P' l = some f)
    (hS : ∀ l, S l → S' l ∨ ∃ f, P l = some f ∧ f ≤ V)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws : List Word} {a : WeakMem.Address}
    (hw : ws.map (·.val) = [.loc a 0]) (hL : LocAbove V ws) :
    ModeOK1 i P S μ l c ws → ModeOK1 i P' S' μ l c ws := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2⟩
    · rcases hS l h2 with h3 | ⟨f', h3, h4⟩
      · exact ⟨f, hP l f h1, Or.inl h3⟩
      · rw [h1, Option.some.injEq] at h3; subst h3
        refine ⟨f, hP l f h1, Or.inr fun w hw' => Nat.le_trans h4 (hL w hw' a 0 ?_)⟩
        have : w.val ∈ ws.map (·.val) := List.mem_map_of_mem hw'
        rw [hw] at this; simpa using this
    · exact ⟨f, hP l f h1, Or.inr h2⟩
  | rgn _ =>
    rintro ⟨f, h1, h2 | h2⟩
    · rcases hS l h2 with h3 | ⟨f', h3, h4⟩
      · exact ⟨f, hP l f h1, Or.inl h3⟩
      · rw [h1, Option.some.injEq] at h3; subst h3
        refine ⟨f, hP l f h1, Or.inr fun w hw' => Nat.le_trans h4 (hL w hw' a 0 ?_)⟩
        have : w.val ∈ ws.map (·.val) := List.mem_map_of_mem hw'
        rw [hw] at this; simpa using this
    · exact ⟨f, hP l f h1, Or.inr h2⟩

theorem VR1_up {ρ : Nat → Nat} {η : TEnv} : ∀ (t : Ty) (rt : Shp) (ws ws' : List Word),
    WLe ws ws' → VR1 ρ η t rt ws → VR1 ρ η t rt ws' := by
  intro t
  induction t generalizing ρ η with
  | tex κ b ih =>
      intro rt ws ws' e hv
      simp only [VR1] at hv ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := hv
      exact ⟨n, rb, s, hr, hs, haf, ih rb ws ws' e hv⟩
  | prod a b iha ihb =>
      intro rt ws ws' e hv
      simp only [VR1] at hv ⊢
      obtain ⟨ra, rb, hr, hf⟩ := hv
      refine ⟨ra, rb, hr, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨e.length ▸ h1, iha ra _ _ (e.take n) h2, ihb rb _ _ (e.drop n) h3⟩
  | iex b ih =>
      intro rt ws ws' e hv
      simp only [VR1] at hv ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := hv
      exact ⟨n, rb, w, hr, ih rb ws ws' e hv⟩
  | refine t ψ ih =>
      intro rt ws ws' e hv; simp only [VR1] at hv ⊢; exact ⟨ih rt ws ws' e hv.1, IniR_vals e.vals ψ hv.2⟩
  | sum a b iha ihb =>
      intro rt ws ws' e hv
      simp only [VR1] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · exact ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, e.vals.symm.trans hx, ho, hB, hn, hsB,
          hm.imp id (WLe_view e hx B.fr), fun hj => ⟨fun e' => iha _ _ _ e ((hA hj).1 e'), (hA hj).2⟩,
          fun hj => ⟨fun e' => ihb _ _ _ e ((hA' hj).1 e'), (hA' hj).2⟩⟩⟩
      · obtain ⟨p', hd', ep⟩ := decodeArm_wle e hd
        refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p', hd', fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', iha _ _ _ eq hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', ihb _ _ _ eq hv⟩
  | mu b ih => intro rt ws ws' e hv; simp only [VR1] at hv ⊢; exact ih rt ws ws' e hv
  | iall b ih => intro rt ws ws' e hv; simp only [VR1] at hv ⊢; exact fun n => ih rt ws ws' e (hv n)
  | tvar k =>
      intro rt ws ws' e hv; simp only [VR1] at hv ⊢
      obtain ⟨w0, h0, hr⟩ := hv
      exact ⟨w0, WLe_trans h0 e, hr⟩
  | ptr μ u =>
      intro rt ws ws' e hv; simp only [VR1] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
        ModeOK1_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | ptrOpt μ u =>
      intro rt ws ws' e hv; simp only [VR1] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl (e.vals.symm.trans hn)
      · exact Or.inr ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
          ModeOK1_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | loc μ u =>
      intro rt ws ws' e hv; simp only [VR1] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨e.vals.symm.trans hn.1, hn.2⟩
      · exact Or.inr ⟨a, c, U, e.vals.symm.trans h1, h3, h4, hF,
          ModeOK1_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | tid =>
      intro rt ws ws' e hv; simp only [VR1] at hv ⊢
      obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
      exact ⟨l, c, e.vals.symm.trans h1, h2, h3,
        ModeOK1_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5⟩
  | _ => intro rt ws ws' e hv; simp only [VR1] at hv ⊢ <;> first | exact hv | (rw [← e.vals]; exact hv)

theorem VR1_mono : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    VR1 ρ η₁ t rt ws → (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) → VR1 ρ η₂ t rt ws
  | .tvar k, η₁, η₂, ρ, rt, ws, hr, hur, _, _, _, _, _, hP, hS, hBx, hv, hri => by
      simp only [VR1, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢; exact ⟨VR1_mono t η₁ η₂ ρ rt ws hr hur hw hp ht hs hi hP hS hBx hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR1_mono b η₁ η₂ (vcons w ρ) rb ws hr hur hw hp ht hs hi hP hS hBx h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VR1_mono a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx e2, VR1_mono b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ h2, h3⟩) id,
          fun hj => ⟨fun e => VR1_mono a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VR1_mono b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR1_mono a η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR1_mono b η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
      · refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, VR1_mono a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj; exact ⟨q, hq, VR1_mono b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hv⟩
  | .code a b _, η₁, η₂, ρ, rt, ws, _, _, hw, hp, _, _, _, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR1_mono b (η₁.push0 s) (η₂.push0 s) ρ rb ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK1_mono hP hS (fun _ x => x) h5, h6⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn
      · exact Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK1_mono hP hS (fun _ x => x) h5, h6⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn.1, hw ▸ hn.2⟩
      · exact Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOK1_mono hP hS (fun _ x => x) h5,
          IniAt_mono (modeIni_le hi hri μ) h6⟩
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .opq _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, _ => by simp only [VR1] at hv ⊢; exact hv
  | .tid, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, hv, _ => by
        simp only [VR1] at hv ⊢
        obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
        exact ⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOK1_mono hP hS (fun _ x => x) h5⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simp [VR1] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR1] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR1]
  | .mu b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      rw [← hw]
      refine VR1_mono b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR1] at hv ⊢
      exact fun n => VR1_mono b η₁ η₂ (vcons n ρ) rt ws hr hur hw hp ht hs hi hP hS hBx (hv n)

/-- `VR_unsee` for `VR1`. -/
theorem VR1_unsee (V : WeakMem.Ts) : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l ∨ ∃ f, η₁.pfr l = some f ∧ f ≤ V) →
    (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    LocAbove V ws → VR1 ρ η₁ t rt ws → (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) → VR1 ρ η₂ t rt ws
  | .tvar k, η₁, η₂, ρ, rt, ws, hr, hur, _, _, _, _, _, _, _, hBx, _, hv, hri => by
      simp only [VR1, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      exact ⟨VR1_unsee V t η₁ η₂ ρ rt ws hr hur hw hp ht hs hi hP hS hBx hL hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR1_unsee V b η₁ η₂ (vcons w ρ) rb ws hr hur hw hp ht hs hi hP hS hBx hL h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VR1_unsee V a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.take n) e2,
        VR1_unsee V b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.drop n) e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, boxSeen_unsee hP hS hx hL hm,
          fun hj => ⟨fun e => VR1_unsee V a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hL ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VR1_unsee V b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hL ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR1_mono a η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR1_mono b η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
      · have hLp := LocAbove_decodeArm hd hL
        refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VR1_unsee V a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VR1_unsee V b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hv⟩
  | .code a b _, η₁, η₂, ρ, rt, ws, _, _, hw, hp, _, _, _, _, _, hBx, _, hv, hri => by
      simp only [VR1] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR1_unsee V b (η₁.push0 s) (η₂.push0 s) ρ rb ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hL h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK1_unsee hP hS h1 hL h5, h6⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn
      · exact Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK1_unsee hP hS h1 hL h5, h6⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn.1, hw ▸ hn.2⟩
      · exact Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOK1_unsee hP hS h1 hL h5,
          IniAt_mono (modeIni_le hi hri μ) h6⟩
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .opq _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, _ => by simp only [VR1] at hv ⊢; exact hv
  | .tid, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, hL, hv, _ => by
        simp only [VR1] at hv ⊢
        obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
        exact ⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOK1_unsee hP hS h1 hL h5⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simp [VR1] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR1] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR1]
  | .mu b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      rw [← hw]
      refine VR1_unsee V b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hL hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR1] at hv ⊢
      exact fun n => VR1_unsee V b η₁ η₂ (vcons n ρ) rt ws hr hur hw hp ht hs hi hP hS hBx hL (hv n)

/-- `EnvVal` over `VR1`. -/
def EnvVal1 (η : TEnv) (T : Ty) (ws : List Word) : Prop :=
  VR1 (fun _ => 0) (CE η) T (shp T) ws ∧ Valid T ws

/-- `ValOf` over `VR1`. -/
def ValOf1 (η : TEnv) (T : Ty) (ws : List Word) : Prop :=
  VR1 (fun _ => 0) (CE η.unsee) T (shp T) ws ∧ Valid T ws

/-- **A value stored is a memory value** over `VR1` (region references included): `EnvVal.store` with
`SeenLE` unchanged. -/
theorem EnvVal1.store {η : TEnv} {T : Ty} {ws : List Word} {V : Ts} (h : EnvVal1 η T ws) (hS : SeenLE η V) :
    ValOf1 η T (ws.map (bumpW V)) :=
  ⟨VR1_unsee V T (CE η) (CE η.unsee) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl)) (fun _ _ h => h) (LocAbove_bump V ws)
      (VR1_up _ _ _ _ (WLe_bump V ws) h.1),
    Valid_vals _ _ _ (WLe_bump V ws).vals h.2⟩

/-- A memory value is a value in the thread's view, over `VR1`. -/
theorem ValOf1.env {η : TEnv} {T : Ty} {ws : List Word} (h : ValOf1 η T ws) : EnvVal1 η T ws :=
  ⟨VR1_mono T (CE η.unsee) (CE η) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h.1, h.2⟩

/-- The `rgn` arm of `ModeOK1` is the `pub` clause (by definition). -/
theorem ModeOK1_rgn_pub (i : Nat) (P : AllocLabel → Option Ts) (S : AllocLabel → Prop) (r : Idx) :
    ModeOK1 i P S (.rgn r) = ModeOK1 i P S .pub := rfl

end TermC1

#print axioms TermC1.ModeOK1_mono
#print axioms TermC1.ModeOK1_unsee
#print axioms TermC1.VR1_up
#print axioms TermC1.VR1_mono
#print axioms TermC1.VR1_unsee
#print axioms TermC1.EnvVal1.store
#print axioms TermC1.ValOf1.env
#print axioms TermC1.ModeOK1_rgn_pub
