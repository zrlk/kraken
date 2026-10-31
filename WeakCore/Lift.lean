import WeakCore.LiftH
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **Lift** (D1/L2): a ♭ reading at `η₁` gives a W reading at `η₂`, of the words relabeled per position
by `gc` (copy at exempt pub positions, `σ` elsewhere), resource pulled back along `σ`. -/

/-- ♭ env `η₁` lifts to W env `η₂`: `σ` maps cells/boxes/ghosts; copies (`cpy`) of the `Cp` labels are
unseen, published at frontier ⊥, carry the original's box, and have `ini`/`rini` from `ini`/`rc`.
`cini`/`crini` are D5-internal: they never reach an exit statement. -/
structure LiftOKQ (cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel) (Cp : WeakMem.AllocLabel → Prop)
    (bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel) (η₁ η₂ : TEnv) : Prop where
  wit : η₂.wit = η₁.wit
  prog : η₂.prog = η₁.prog
  tid : η₂.tid = η₁.tid
  sl : ∀ m, τ (σ m) = m
  sr : ∀ m, σ (τ m) = m
  sto : ∀ l c, η₁.sto l = some c → η₂.sto (σ l) = some c
  ini : ∀ l, η₁.ini l ≤ η₂.ini (σ l)
  rini : ∀ l, η₁.rini l ≤ η₂.rini (σ l)
  pfr : ∀ l q, η₁.pfr l = some q → η₂.pfr (σ l) = some q
  seen : ∀ l, η₁.seen l → η₂.seen (σ l)
  cown : ∀ l c, η₁.sto l = some c → c.owner = some η₁.tid → (∃ q, η₁.pfr l = some q) → Cp l
  csto : ∀ l c, Cp l → η₁.sto l = some c → ∃ c₂, η₂.sto (cpy l) = some c₂ ∧ c₂.ty = c.ty
  crini : ∀ l, Cp l → η₁.rc l ≤ η₂.rini (cpy l)
  cpfr : ∀ l, Cp l → ∃ f, η₂.pfr (cpy l) = some f ∧ ∀ v : WeakMem.Ts, f ≤ v
  -- a box at `σ l` / `cpy l` with `l`'s header; the payload is unconstrained apart from its length
  -- (weaker than the earlier `box`/`cbox`).  Used only at a boxed-sum pointer whose arm is itself boxed, where W reads
  -- no payload.
  box : ∀ l B, η₁.box l = some B → ∃ P : List Word, P.length = B.pay.length ∧ η₂.box (σ l) = some { B with pay := P }
  cbox : ∀ l B, Cp l → η₁.box l = some B →
    ∃ P : List Word, P.length = B.pay.length ∧ η₂.box (cpy l) = some { B with pay := P }
  -- box variants: for every ♭ box `x` and every payload-map code `k`
  vbox : ∀ x B k, η₁.box x = some B → η₂.box (bv x k) = some { B with pay := rlI (PCode.dec σ cpy bv k) B.pay }
  vpfr : ∀ x k q, η₁.pfr x = some q → η₂.pfr (bv x k) = some q
  vseen : ∀ x k, η₁.seen x → η₂.seen (bv x k)
  vini : ∀ x k, η₁.ini x ≤ η₂.ini (bv x k)
  vrini : ∀ x k, η₁.rini x ≤ η₂.rini (bv x k)

/-- (LiftCini′, restated) the copy's `ini` dominates the original's `rc`
(the copy is seeded with `rc`, so this holds by construction; it is not a temporary). -/
def LiftCini (cpy : WeakMem.AllocLabel → WeakMem.AllocLabel) (Cp : WeakMem.AllocLabel → Prop) (η₁ η₂ : TEnv) : Prop :=
  ∀ l, Cp l → η₁.rc l ≤ η₂.ini (cpy l)

/-- `E` reads like `η` for `gc` (boxes, frontiers, seen). -/
def SameV (E η : TEnv) : Prop := E.box = η.box ∧ E.pfr = η.pfr ∧ E.seen = η.seen

/-- The type-variable lift: each ♭ variable reading (either `VRRB` disjunct) lifts under `T`. -/
def TvL (τ : WeakMem.AllocLabel → WeakMem.AllocLabel)
    (T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (η₁ η₂ : TEnv) : Prop :=
  ∀ k rt ws' ws R, WLe ws' ws →
    (η₁.rrs k rt ws' R ∨ (VRRz (fun _ => 0) (CE η₁) (η₁.wit k) rt ws' R ∧ R = .zero ∧
      ∃ S0 w0 R0, η₁.rrs k S0 w0 R0)) →
    ∃ ws'', WLe ws'' (rlI (T k rt ws) ws) ∧ η₂.rrs k rt ws'' (Res.sw τ R)

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem LiftOKQ.push0 {η₁ η₂ : TEnv} (h : LiftOKQ cpy σ τ Cp bv η₁ η₂) (s : Ty) :
    LiftOKQ cpy σ τ Cp bv (η₁.push0 s) (η₂.push0 s) :=
  { wit := by simp [TEnv.push0, TEnv.ins, TEnv.insR, h.wit], prog := h.prog, tid := h.tid, sl := h.sl, sr := h.sr,
    sto := h.sto, ini := h.ini, rini := h.rini, pfr := h.pfr, seen := h.seen, cown := h.cown,
    csto := h.csto, crini := h.crini, cpfr := h.cpfr, box := h.box, cbox := h.cbox, vbox := h.vbox, vpfr := h.vpfr, vseen := h.vseen,
    vini := h.vini, vrini := h.vrini }

theorem LiftOKQ.unsee {η₁ η₂ : TEnv} (h : LiftOKQ cpy σ τ Cp bv η₁ η₂) :
    LiftOKQ cpy σ τ Cp bv η₁.unsee η₂.unsee :=
  { wit := h.wit, prog := h.prog, tid := h.tid, sl := h.sl, sr := h.sr,
    sto := h.sto, ini := h.ini, rini := h.rini, pfr := h.pfr, seen := fun _ hs => hs.elim, cown := h.cown,
    csto := h.csto, crini := h.crini, cpfr := h.cpfr, box := h.box, cbox := h.cbox, vbox := h.vbox, vpfr := h.vpfr, vseen := fun _ _ hs => hs.elim,
    vini := h.vini, vrini := h.vrini }

theorem LiftCini.push0 {η₁ η₂ : TEnv} (h : LiftCini cpy Cp η₁ η₂) (s : Ty) :
    LiftCini cpy Cp (η₁.push0 s) (η₂.push0 s) := h
theorem LiftCini.unsee {η₁ η₂ : TEnv} (h : LiftCini cpy Cp η₁ η₂) : LiftCini cpy Cp η₁.unsee η₂.unsee := h

theorem unsee_unsee (η : TEnv) : η.unsee.unsee = η.unsee := rfl
theorem push0_unsee (η : TEnv) (s : Ty) : (η.push0 s).unsee = η.unsee.push0 s := rfl
theorem SameV.unsee {E η : TEnv} (h : SameV E η) : SameV E.unsee η.unsee :=
  ⟨h.1, h.2.1, rfl⟩

theorem TvL.push0 {T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {η₁ η₂ : TEnv}
    (h : TvL τ T η₁ η₂) (s : Ty) : TvL τ (shT σ T) (η₁.push0 s) (η₂.push0 s) := by
  intro k rt ws' ws R hw hor
  cases k with
  | zero =>
    exfalso
    rcases hor with h0 | ⟨-, -, S0, w0, R0, h0⟩ <;> simp [TEnv.push0, TEnv.ins, TEnv.insR] at h0
  | succ k =>
    have hor' : η₁.rrs k rt ws' R ∨ (VRRz (fun _ => 0) (CE η₁) (η₁.wit k) rt ws' R ∧ R = .zero ∧
        ∃ S0 w0 R0, η₁.rrs k S0 w0 R0) := by
      rcases hor with h0 | ⟨h1, h2, S0, w0, R0, h0⟩
      · left; simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h0
      · right; refine ⟨h1, h2, S0, w0, R0, ?_⟩
        simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h0
    obtain ⟨ws'', h1, h2⟩ := h k rt ws' ws R hw hor'
    exact ⟨ws'', h1, by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h2⟩

theorem selIni_lift {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (t : Ty)
    (l : WeakMem.AllocLabel) (g : WeakMem.AllocLabel → WeakMem.AllocLabel)
    (hg : g = σ ∨ ∃ k, g = fun y => bv y k) :
    η₁.selIni t l ≤ η₂.selIni t (g l) := by
  unfold TEnv.selIni
  rw [ownTop_eq hm.wit t]
  rcases hg with rfl | ⟨k, rfl⟩
  · have h1 := hm.ini l; have h2 := hm.rini l
    split <;> (try dsimp only) <;> omega
  · have h1 := hm.vini l k; have h2 := hm.vrini l k
    split <;> (try dsimp only) <;> omega

/-- (rc seed) At a copy, the W `selIni` dominates the original's `rc`. -/
theorem selIni_cpy {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂) (t : Ty)
    {l : WeakMem.AllocLabel} (hc : Cp l) : η₁.rc l ≤ η₂.selIni t (cpy l) := by
  unfold TEnv.selIni
  have h1 := hci l hc; have h2 := hm.crini l hc
  split <;> (try dsimp only) <;> omega

end
end TermSound.Flat
