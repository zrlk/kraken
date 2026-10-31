import WeakCore.PubPos
/-! The two-level `VRb2`, with the `.ptr`/`.ptrOpt` arms' flag `bk ∨ (cell is not a buffer)`.
(η.get closure; route (D), step S1b).  Generated from VR
(TermSound:1412–1481) as for `VRb`, plus the `.tvar` arm
`∃ ws', WLe ws' ws ∧ (η.get k rt ws' ∨ VRz (fun _ => 0) (CE η) bk (η.wit k) rt ws')` — Z‴: the inner `VRz`
(VRb2 with W's plain `.tvar` arm, same generator pass) reads the closed witness at the common env, so an exempt word can sit at a type variable;
the left disjunct keeps `VR ⇒ VRb2` free of `Coh`.  `VRB` is the top-level (flag `False`) form used by
the generated frame layer (the port renames VR ↦ VRB). -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-- Z″: a word list is *fresh* if, read as a reference into `a`, `a` is published (`pfr`) and either
seen or below the word views (what `ModeOK .pub` gives without the exemption). -/
def FreshW (η : TEnv) (ws : List Word) : Prop :=
  ∀ a : WeakMem.Address, ws.map (·.val) = [.loc a 0] → ∃ f, η.pfr a.label = some f ∧
    (η.seen a.label ∨ ∀ w ∈ ws, f ≤ w.view)

/-- Z″: a `pub` reference at the syntactic head. -/
def _root_.CoreLang.Ty.pubHead : Ty → Bool
  | .loc .pub _ | .ptr .pub _ | .ptrOpt .pub _ => true
  | _ => false

/-- F1: the pub head seen through a type variable (its witness), as W's `TEnv.ownTop`. -/
def _root_.TermSound.TEnv.pubTop (η : TEnv) : Ty → Bool
  | .tvar k => (η.wit k).pubHead
  | t => t.pubHead

def VRz (ρ : Nat → Nat) (η : TEnv) : Prop → Ty → Shp → List Word → Prop
  | _bk, .intS i, _, ws => ws.map (·.val) = [.num (ev ρ i)]
  | _bk, .int, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | _bk, .opq _, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | _bk, .tid, _, ws => ∃ l c, ws.map (·.val) = [.loc ⟨l, 0⟩ 0] ∧ η.sto l = some c ∧ c.ty = .unit ∧
      ModeOKb η.tid η.pfr η.seen (∀ N e, c.ty ≠ .array (.lit N) e) .pub l c ws
  | _bk, .fix sg w, rt, ws => rt = .fix sg w ∧ ∃ n, ws.map (·.val) = [.num n] ∧ n < pw2 w
  | _bk, .lanes sg w, rt, ws => rt = .lanes sg w ∧ ∃ n, ws.map (·.val) = [.num n]
  | bk, .refine t ψ, rt, ws => VRz ρ η bk t rt ws ∧ IniR ρ (η.selIni t) ψ ws ∧
      (PubPosE η t rt ws → FreshW η ws ∨ IniR ρ η.rc ψ ws)
  | bk, .iex b, rt, ws => ∃ n rb w, rt = .iex n rb ∧ VRz (vcons w ρ) η bk b rb ws
  | _bk, .prod a b, rt, ws => ∃ ra rb, rt = .prod ra rb ∧ ∀ n, ra.wc = some n →
      n ≤ ws.length ∧ VRz ρ η False a ra (ws.take n) ∧ VRz ρ η False b rb (ws.drop n)
  -- T3c-5d: a boxed sum is a reference to a box whose payload, re-injected into
  -- the summand its tag (less the offset `s`) selects, is a value there; a boxed
  -- summand is read through the same reference, its tag offset further (`vsh`)
  | _bk, .sum a b, rt, ws => ∃ n Ra Rb, rt = .sum n (.sum Ra Rb) ∧
      (((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x s B, ws.map (·.val) = [.loc x 0] ∧ x.offset = 0 ∧
          η.box x.label = some B ∧ n = some (s + 1) ∧
          (s ≤ B.tag ∧ ((armsOf (.sum Ra Rb))[B.tag - s]?).bind wc = some B.pay.length) ∧
          ((η.seen x.label ∧ ∃ f, η.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) ∧
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VRz ρ η False a (vsh s (shp Ra)) ws) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) B.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VRz ρ η.unsee False a (shp Ra) q)) ∧
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VRz ρ η False b (vsh (s + (armsOf Ra).length) (shp Rb)) ws) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VRz ρ η.unsee False b (shp Rb) q))) ∨ ∃ j p,
        decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws = some (j, p) ∧
        (j < (armsOf Ra).length → ∃ q, ofArm Ra j p = some q ∧ VRz ρ η False a (shp Ra) q) ∧
        ((armsOf Ra).length ≤ j → ∃ q, ofArm Rb (j - (armsOf Ra).length) p = some q ∧ VRz ρ η False b (shp Rb) q))
  | _bk, .tvar k, rt, ws => ∃ ws', WLe ws' ws ∧ η.get k rt ws'
  | _bk, .code σ τ _, rt, ws => ∃ i d, ws.map (·.val) = [.num i] ∧ η.prog[i]? = some d ∧
      η.prog.find? (·.name == d.name) = some d ∧ d.tparams = [] ∧ d.idx = [] ∧
      cl ρ η.wit 0 0 σ = clD d.argTy ∧ cl ρ η.wit 0 0 τ = clD d.retTy
  -- T3c-3: a reference's cell is in Σ, holds exactly the closure of the target
  -- type (invariant: no strong update), and agrees with the mode
  | bk, .ptr μ u, _, ws => ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
      Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ ∀ N e, c.ty ≠ .array (.lit N) e) μ a.label c ws ∧ accs c.ty ≠ none
  -- F5: `null` is a locative only to a zero-length array (`zeroableIn`), which
  -- no access reaches (T3c-5a)
  | bk, .loc μ u, _, ws => (ws.map (·.val) = [.null] ∧ ∃ e, Fd (.array (.lit 0) e) (cl ρ η.wit 0 0 u)) ∨
      ∃ a c U, ws.map (·.val) = [.loc a 0] ∧ η.sto a.label = some c ∧
        AtOff c.ty a.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ IniAt η.rc c a U) μ a.label c ws ∧
          IniAt (modeIni μ η.ini η.rini) c a U
  | bk, .ptrOpt μ u, _, ws => ws.map (·.val) = [.null] ∨
      ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
        Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ ∀ N e, c.ty ≠ .array (.lit N) e) μ a.label c ws ∧ accs c.ty ≠ none
  | _bk, .void, _, _ => False
  -- T3c: some closed witness `s`; its variable has no values (`push0`), which
  -- `guardT` keeps where `VR` reads only witnesses (code signatures, and from
  -- T3c-3 reference targets)
  | bk, .tex κ b, rt, ws => ∃ n rb s, rt = .tex n rb ∧ Clo s ∧ WitOK κ s ∧ VRz ρ (η.push0 s) bk b rb ws
  -- T3c-5a: the body, its variable the closed `μ` type itself; the
  -- variable is guarded (`guardT`), so its (empty, `push0`) relation is never
  -- read, and `VR` at a reference to it compares with the witness
  | bk, .mu b, rt, ws => VRz ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) bk b rt ws
  -- T3c-5f: indices are erased, so a value of `∀i. b` is, on the same words, a
  -- value of `b` at every index
  | bk, .iall b, rt, ws => ∀ n, VRz (vcons n ρ) η bk b rt ws
  -- T3d-1: a protocol word's protocol is well formed (`mkWord` checks it), and a
  -- runtime word holds a state of it
  | _bk, .word _ P, _, ws => pwf P = true ∧ (P.ghost = false → ∃ n, ws.map (·.val) = [.num n] ∧ InP P n)
  -- T3d-1: a protocol pair holds a pair state (`mkWord2`, `stp` and `casp`
  -- check one); an epoch pair holds two numbers (`caspE` writes the live
  -- token's epoch and an arbitrary value, so nothing stronger is invariant)
  | _bk, .word2 _ P, _, ws => pwf2 P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] ∧ InP2 P n0 n1
  | _bk, .epair _ P, _, ws => pwfE P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1]
  | _bk, _, _, _ => True


def VRb2 (ρ : Nat → Nat) (η : TEnv) : Prop → Ty → Shp → List Word → Prop
  | _bk, .intS i, _, ws => ws.map (·.val) = [.num (ev ρ i)]
  | _bk, .int, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | _bk, .opq _, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | _bk, .tid, _, ws => ∃ l c, ws.map (·.val) = [.loc ⟨l, 0⟩ 0] ∧ η.sto l = some c ∧ c.ty = .unit ∧
      ModeOKb η.tid η.pfr η.seen (∀ N e, c.ty ≠ .array (.lit N) e) .pub l c ws
  | _bk, .fix sg w, rt, ws => rt = .fix sg w ∧ ∃ n, ws.map (·.val) = [.num n] ∧ n < pw2 w
  | _bk, .lanes sg w, rt, ws => rt = .lanes sg w ∧ ∃ n, ws.map (·.val) = [.num n]
  | bk, .refine t ψ, rt, ws => VRb2 ρ η bk t rt ws ∧ IniR ρ (η.selIni t) ψ ws ∧
      (PubPosE η t rt ws → FreshW η ws ∨ IniR ρ η.rc ψ ws)
  | bk, .iex b, rt, ws => ∃ n rb w, rt = .iex n rb ∧ VRb2 (vcons w ρ) η bk b rb ws
  | _bk, .prod a b, rt, ws => ∃ ra rb, rt = .prod ra rb ∧ ∀ n, ra.wc = some n →
      n ≤ ws.length ∧ VRb2 ρ η False a ra (ws.take n) ∧ VRb2 ρ η False b rb (ws.drop n)
  -- T3c-5d: a boxed sum is a reference to a box whose payload, re-injected into
  -- the summand its tag (less the offset `s`) selects, is a value there; a boxed
  -- summand is read through the same reference, its tag offset further (`vsh`)
  | _bk, .sum a b, rt, ws => ∃ n Ra Rb, rt = .sum n (.sum Ra Rb) ∧
      (((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x s B, ws.map (·.val) = [.loc x 0] ∧ x.offset = 0 ∧
          η.box x.label = some B ∧ n = some (s + 1) ∧
          (s ≤ B.tag ∧ ((armsOf (.sum Ra Rb))[B.tag - s]?).bind wc = some B.pay.length) ∧
          ((η.seen x.label ∧ ∃ f, η.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) ∧
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VRb2 ρ η False a (vsh s (shp Ra)) ws) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) B.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VRb2 ρ η.unsee False a (shp Ra) q)) ∧
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VRb2 ρ η False b (vsh (s + (armsOf Ra).length) (shp Rb)) ws) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VRb2 ρ η.unsee False b (shp Rb) q))) ∨ ∃ j p,
        decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws = some (j, p) ∧
        (j < (armsOf Ra).length → ∃ q, ofArm Ra j p = some q ∧ VRb2 ρ η False a (shp Ra) q) ∧
        ((armsOf Ra).length ≤ j → ∃ q, ofArm Rb (j - (armsOf Ra).length) p = some q ∧ VRb2 ρ η False b (shp Rb) q))
  | bk, .tvar k, rt, ws => ∃ ws', WLe ws' ws ∧ (η.get k rt ws' ∨ (VRz (fun _ => 0) (CE η) bk (η.wit k) rt ws' ∧ ∃ S0 w0, η.rels k S0 w0))
  | _bk, .code σ τ _, rt, ws => ∃ i d, ws.map (·.val) = [.num i] ∧ η.prog[i]? = some d ∧
      η.prog.find? (·.name == d.name) = some d ∧ d.tparams = [] ∧ d.idx = [] ∧
      cl ρ η.wit 0 0 σ = clD d.argTy ∧ cl ρ η.wit 0 0 τ = clD d.retTy
  -- T3c-3: a reference's cell is in Σ, holds exactly the closure of the target
  -- type (invariant: no strong update), and agrees with the mode
  | bk, .ptr μ u, _, ws => ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
      Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ ∀ N e, c.ty ≠ .array (.lit N) e) μ a.label c ws ∧ accs c.ty ≠ none
  -- F5: `null` is a locative only to a zero-length array (`zeroableIn`), which
  -- no access reaches (T3c-5a)
  | bk, .loc μ u, _, ws => (ws.map (·.val) = [.null] ∧ ∃ e, Fd (.array (.lit 0) e) (cl ρ η.wit 0 0 u)) ∨
      ∃ a c U, ws.map (·.val) = [.loc a 0] ∧ η.sto a.label = some c ∧
        AtOff c.ty a.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ IniAt η.rc c a U) μ a.label c ws ∧
          IniAt (modeIni μ η.ini η.rini) c a U
  | bk, .ptrOpt μ u, _, ws => ws.map (·.val) = [.null] ∨
      ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
        Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ ∀ N e, c.ty ≠ .array (.lit N) e) μ a.label c ws ∧ accs c.ty ≠ none
  | _bk, .void, _, _ => False
  -- T3c: some closed witness `s`; its variable has no values (`push0`), which
  -- `guardT` keeps where `VR` reads only witnesses (code signatures, and from
  -- T3c-3 reference targets)
  | bk, .tex κ b, rt, ws => ∃ n rb s, rt = .tex n rb ∧ Clo s ∧ WitOK κ s ∧ VRb2 ρ (η.push0 s) bk b rb ws
  -- T3c-5a: the body, its variable the closed `μ` type itself; the
  -- variable is guarded (`guardT`), so its (empty, `push0`) relation is never
  -- read, and `VR` at a reference to it compares with the witness
  | bk, .mu b, rt, ws => VRb2 ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) bk b rt ws
  -- T3c-5f: indices are erased, so a value of `∀i. b` is, on the same words, a
  -- value of `b` at every index
  | bk, .iall b, rt, ws => ∀ n, VRb2 (vcons n ρ) η bk b rt ws
  -- T3d-1: a protocol word's protocol is well formed (`mkWord` checks it), and a
  -- runtime word holds a state of it
  | _bk, .word _ P, _, ws => pwf P = true ∧ (P.ghost = false → ∃ n, ws.map (·.val) = [.num n] ∧ InP P n)
  -- T3d-1: a protocol pair holds a pair state (`mkWord2`, `stp` and `casp`
  -- check one); an epoch pair holds two numbers (`caspE` writes the live
  -- token's epoch and an arbitrary value, so nothing stronger is invariant)
  | _bk, .word2 _ P, _, ws => pwf2 P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] ∧ InP2 P n0 n1
  | _bk, .epair _ P, _, ws => pwfE P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1]
  | _bk, _, _, _ => True



/-- The generated layer's `VR`: `VRb2` at flag `False`. -/
theorem ModeOKb_flag {i P S} {bk bk' : Prop} (hb : bk → bk') {μ l c ws} (h : ModeOKb i P S bk μ l c ws) :
    ModeOKb i P S bk' μ l c ws := by
  cases μ with
  | pub => obtain ⟨f, hf, h⟩ := h; exact ⟨f, hf, h.imp id (Or.imp id (And.imp id hb))⟩
  | _ => exact h

theorem VRb_flag (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (bk bk' : Prop) (rt : Shp) (ws : List Word),
    (bk → bk') → VRb ρ η bk t rt ws → VRb ρ η bk' t rt ws := by
  induction t with
  | tid => intro ρ η bk bk' rt ws _ h; exact h
  | refine t ψ ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    exact ⟨ih _ _ _ _ _ _ (Or.imp_left hb) h.1, h.2⟩
  | iex b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ _ hb hv⟩
  | ptr μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    obtain ⟨a, c, h1, h2, h3, h4, hm, h5⟩ := h; exact ⟨a, c, h1, h2, h3, h4, ModeOKb_flag hb hm, h5⟩
  | ptrOpt μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    rcases h with h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, h1, h2, h3, h4, ModeOKb_flag hb hm, h5⟩
  | loc μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    rcases h with h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | tex κ b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ _ hb hv⟩
  | mu b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    exact ih _ _ _ _ _ _ hb h
  | iall b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb] at h ⊢
    exact fun n => ih _ _ _ _ _ _ hb (h n)
  | _ => intro ρ η bk bk' rt ws _ h; exact h

def VRB (ρ : Nat → Nat) (η : TEnv) (t : Ty) (rt : Shp) (ws : List Word) : Prop := VRb2 ρ η False t rt ws

theorem VR_pubFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hp : t.pubHead = true)
    (h : VR ρ η t rt ws) : FreshW η ws := by
  intro a' ha'
  match t, hp, h with
  | .ptr .pub u, _, h =>
    simp only [VR] at h; obtain ⟨a, c, h1, -, -, -, hm, -⟩ := h
    obtain rfl : a = a' := by have := h1.symm.trans ha'; simpa using this
    exact hm
  | .ptrOpt .pub u, _, h =>
    simp only [VR] at h
    rcases h with h | ⟨a, c, h1, -, -, -, hm, -⟩
    · rw [h] at ha'; simp at ha'
    · obtain rfl : a = a' := by have := h1.symm.trans ha'; simpa using this
      exact hm
  | .loc .pub u, _, h =>
    simp only [VR] at h
    rcases h with h | ⟨a, c, U, h1, -, -, -, hm, -⟩
    · rw [h.1] at ha'; simp at ha'
    · obtain rfl : a = a' := by have := h1.symm.trans ha'; simpa using this
      exact hm

/-- F1-a: the frame relations are sound for W's strict `VR` at their witnesses (what W `Coh` gives). -/
def RelsSound (η : TEnv) : Prop :=
  (∀ k S ws, η.rels k S ws → VR (fun _ => 0) (CE η) (η.wit k) S ws) ∧
  (∀ k S ws, η.urels k S ws → VR (fun _ => 0) (CE η.unsee) (η.wit k) S ws)

theorem RelsSound.of_Coh {η : TEnv} (hc : Coh η) : RelsSound η :=
  ⟨fun k S ws h => ((hc k).2.1 _ S ws).1 h, fun k S ws h => ((hc k).2.2 _ S ws).1 h⟩

theorem RelsSound.unsee {η : TEnv} (hR : RelsSound η) : RelsSound η.unsee := ⟨hR.2, hR.2⟩

theorem RelsSound.push0 {η : TEnv} (hR : RelsSound η) (s : Ty) : RelsSound (η.push0 s) := by
  have ew : ∀ k, (η.push0 s).wit (k + 1) = η.wit k := fun k => by simp [TEnv.push0, TEnv.ins, TEnv.insR]
  constructor
  · intro k S ws h
    cases k with
    | zero => rw [push0_rels_zero] at h; exact h.elim
    | succ k => rw [push0_rels_succ] at h; rw [ew]; exact hR.1 k S ws h
  · intro k S ws h
    cases k with
    | zero => rw [push0_urels_zero] at h; exact h.elim
    | succ k => rw [push0_urels_succ] at h; rw [ew]; exact hR.2 k S ws h

theorem FreshW_wle {η : TEnv} {ws ws' : List Word} (e : WLe ws ws') (h : FreshW η ws) : FreshW η ws' := by
  intro a h'
  have hv : ws.map (·.val) = [.loc a 0] := e.vals.trans h'
  obtain ⟨f, hf, hs⟩ := h a hv
  exact ⟨f, hf, hs.imp id (WLe_view e hv f)⟩

/-- F1-a: W `VR` at a pub head seen through a variable is fresh (the `.tvar` case via `RelsSound`). -/
theorem VR_pubTopFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hR : RelsSound η)
    (hp : η.pubTop t = true) (h : VR ρ η t rt ws) : FreshW η ws := by
  cases t with
  | tvar k =>
    simp only [VR, TEnv.get] at h
    obtain ⟨w0, h0, h1⟩ := h
    exact FreshW_wle h0 (VR_pubFresh (η := CE η) hp (hR.1 k rt w0 h1))
  | _ => refine VR_pubFresh ?_ h; exact hp

/-- Freshness of the word at position `i` (a loc word there is published, and seen or below
its view). -/
def FreshAt (η : TEnv) (ws : List Word) (i : Nat) : Prop :=
  ∀ w a g, ws[i]? = some w → w.val = .loc a g → ∃ f, η.pfr a.label = some f ∧ (η.seen a.label ∨ f ≤ w.view)

theorem FreshAt_head {η : TEnv} {ws : List Word} {a : WeakMem.Address} {g : Nat}
    (hv : ws.map (·.val) = [.loc a g])
    (hm : ∃ f, η.pfr a.label = some f ∧ (η.seen a.label ∨ ∀ w ∈ ws, f ≤ w.view)) (i : Nat) : FreshAt η ws i := by
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩ <;> simp at hv
  intro w1 a1 g1 h1 hv1
  rcases i with _ | i <;> simp at h1
  subst h1
  rw [hv] at hv1; cases hv1
  obtain ⟨f, hf, hs⟩ := hm
  exact ⟨f, hf, hs.imp id (fun h => h w (by simp))⟩

theorem FreshAt_null {η : TEnv} {ws : List Word} (hv : ws.map (·.val) = [.null]) (i : Nat) : FreshAt η ws i := by
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩ <;> simp at hv
  intro w1 a1 g1 h1 hv1
  rcases i with _ | i <;> simp at h1
  subst h1; rw [hv] at hv1; cases hv1

theorem FreshW_of_at0 {η : TEnv} {ws : List Word} (h : FreshAt η ws 0) : FreshW η ws := by
  intro a hv
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩ <;> simp at hv
  obtain ⟨f, hf, hs⟩ := h w a 0 rfl hv
  exact ⟨f, hf, hs.imp id (fun h w1 hw1 => by simp at hw1; subst hw1; exact h)⟩

theorem dec_corr {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (hd : decodeArm tr as ws = some (j, p)) (hp : p ≠ []) :
    ∀ i w a g, ws[i]? = some w → w.val = .loc a g →
      ∃ w' g', p[ixU tr i]? = some w' ∧ w'.val = .loc a g' ∧ w'.view = w.view := by
  intro i w a g hw hv
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩
  · simp at hw
  · have hi : i = 0 := by cases i <;> simp_all
    subst hi; simp at hw; subst hw
    cases tr <;> simp [decodeArm, hv] at hd
    cases hx : (List.filter (fun p => isPtrish p.snd) (enumFrom as 0))[g]? <;> simp [hx] at hd
    obtain ⟨-, rfl⟩ := hd; exact ⟨_, 0, rfl, rfl, rfl⟩
  · cases tr <;> simp [decodeArm] at hd
    split at hd
    · rename_i j0 hj0
      cases hx : as[j0]? <;> simp [hx] at hd
      split at hd
      · simp at hd; exact absurd hd.2 hp
      · simp at hd; obtain ⟨-, rfl⟩ := hd
        rcases i with _ | _ | i
        · simp at hw; subst hw; rw [hv] at hj0; cases hj0
        · simp at hw; subst hw; exact ⟨_, g, rfl, hv, rfl⟩
        · simp at hw
    · simp at hd
  · cases tr <;> simp [decodeArm] at hd

theorem ofArm_corr {t : Ty} {j : Nat} {p q : List Word} (hq : ofArm t j p = some q) :
    ∀ k w a g, p[k]? = some w → w.val = .loc a g →
      ∃ w' g', q[ixA t k]? = some w' ∧ w'.val = .loc a g' ∧ w'.view = w.view := by
  intro k w a g hw hv
  unfold ofArm at hq
  unfold ixA
  by_cases hs : sumHead t = true
  · simp only [hs, if_true] at hq
    cases htr : t.tier <;> rw [htr] at hq <;> simp only [encodeArm] at hq
    · rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
      · simp at hw
      · have hk : k = 0 := by cases k <;> simp_all
        subst hk; simp at hw; subst hw
        cases hx : (armsOf t)[j]? <;> simp [hx] at hq
        split at hq
        · rename_i _ h2; simp at h2; subst h2; simp [hv] at hq; subst hq; exact ⟨⟨.loc a (List.filter isPtrish (List.take j (armsOf t))).length, w0.view, w0.rts⟩, _, by simp, rfl, rfl⟩
        · rename_i _ h2; simp at h2; subst h2; simp [hv] at hq; subst hq; exact ⟨⟨.loc a (List.filter isPtrish (List.take j (armsOf t))).length, w0.view, w0.rts⟩, _, by simp, rfl, rfl⟩
        · rename_i _ h2; simp at h2
        · simp at hq
      · cases hx : (armsOf t)[j]? <;> simp [hx] at hq
    · rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
      · simp at hw
      · have hk : k = 0 := by cases k <;> simp_all
        subst hk; simp at hw; subst hw
        simp at hq; subst hq; exact ⟨_, g, by simp [hs, htr], hv, rfl⟩
      · simp at hq
    · simp at hq
  · simp only [hs, if_false, Bool.false_eq_true, false_and] at hq ⊢
    split at hq
    · simp at hq; subst hq; exact ⟨w, g, hw, hv, rfl⟩
    · simp at hq

/-- **W `VR` is fresh at every pub position** (`pp`, per position, generalizing the tvar
oracle `PT`; the word shapes come from the `VR` fact). -/
theorem VR_ppFresh (bx : WeakMem.AllocLabel → Option Box) (t : Ty) : ∀ (PT : Nat → Shp → List Word → Nat → Bool)
    (ρ : Nat → Nat) (η : TEnv) (rt : Shp) (ws : List Word) (i : Nat),
    (∀ l B, η.box l = some B → bx l = some B) →
    (∀ k rt ws i, PT k rt ws i = true → ∀ w0, WLe w0 ws → η.rels k rt w0 → FreshAt η ws i) →
    VR ρ η t rt ws → pp PT bx t rt ws i = true → FreshAt η ws i := by
  induction t with
  | ptr μ u =>
    intro PT ρ η rt ws i _ _ hv hp
    cases μ <;> simp [pp] at hp
    simp only [VR] at hv
    obtain ⟨a, c, h1, -, -, -, hm, -⟩ := hv
    exact FreshAt_head h1 hm i
  | ptrOpt μ u =>
    intro PT ρ η rt ws i _ _ hv hp
    cases μ <;> simp [pp] at hp
    simp only [VR] at hv
    rcases hv with hn | ⟨a, c, h1, -, -, -, hm, -⟩
    · exact FreshAt_null hn i
    · exact FreshAt_head h1 hm i
  | loc μ u =>
    intro PT ρ η rt ws i _ _ hv hp
    cases μ <;> simp [pp] at hp
    simp only [VR] at hv
    rcases hv with ⟨hn, -⟩ | ⟨a, c, U, h1, -, -, -, hm, -⟩
    · exact FreshAt_null hn i
    · exact FreshAt_head h1 hm i
  | tid =>
    intro PT ρ η rt ws i _ _ hv _
    simp only [VR] at hv
    obtain ⟨l, c, h1, -, -, hm⟩ := hv
    exact FreshAt_head h1 hm i
  | refine t ψ ih =>
    intro PT ρ η rt ws i hbx hPT hv hp
    exact ih PT ρ η rt ws i hbx hPT hv.1 hp
  | iall b ih =>
    intro PT ρ η rt ws i hbx hPT hv hp
    exact ih PT (vcons 0 ρ) η rt ws i hbx hPT (hv 0) hp
  | iex b ih =>
    intro PT ρ η rt ws i hbx hPT hv hp
    simp only [VR] at hv
    obtain ⟨n, rb, w, rfl, hv⟩ := hv
    exact ih PT (vcons w ρ) η rb ws i hbx hPT hv hp
  | tvar k =>
    intro PT ρ η rt ws i hbx hPT hv hp
    simp only [VR, TEnv.get] at hv
    obtain ⟨w0, h0, h1⟩ := hv
    exact hPT k rt ws i hp w0 h0 h1
  | tex κ b ih =>
    intro PT ρ η rt ws i hbx hPT hv hp
    simp only [VR] at hv
    obtain ⟨n, rb, s, rfl, -, -, hv⟩ := hv
    have := ih (shPT PT) ρ (η.push0 s) rb ws i hbx (fun k rt ws i hq w0 h0 hr => by
      cases k with
      | zero => simp [shPT] at hq
      | succ k => rw [push0_rels_succ] at hr; exact hPT k rt ws i hq w0 h0 hr) hv hp
    exact this
  | mu b ih =>
    intro PT ρ η rt ws i hbx hPT hv hp
    simp only [VR] at hv
    have := ih (shPT PT) ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) rt ws i hbx (fun k rt ws i hq w0 h0 hr => by
      cases k with
      | zero => simp [shPT] at hq
      | succ k => rw [push0_rels_succ] at hr; exact hPT k rt ws i hq w0 h0 hr) hv hp
    exact this
  | prod a b iha ihb =>
    intro PT ρ η rt ws i hbx hPT hv hp
    simp only [VR] at hv
    obtain ⟨ra, rb, rfl, hf⟩ := hv
    cases hn : ra.wc with
    | none => simp [pp, hn] at hp
    | some n =>
      obtain ⟨-, h1, h2⟩ := hf n hn
      simp only [pp, hn] at hp
      by_cases hi : i < n
      · simp only [hi, if_true] at hp
        have := iha PT ρ η ra (ws.take n) i hbx hPT h1 hp
        intro w a' g hw hv'
        exact this w a' g (by rw [List.getElem?_take]; simp [hi, hw]) hv'
      · simp only [hi, if_false] at hp
        have := ihb PT ρ η rb (ws.drop n) (i - n) hbx hPT h2 hp
        intro w a' g hw hv'
        exact this w a' g (by rw [List.getElem?_drop, Nat.add_sub_cancel' (by omega)]; exact hw) hv'
  | sum a b iha ihb =>
    intro PT ρ η rt ws i hbx hPT hv hp
    simp only [VR] at hv
    obtain ⟨n, Ra, Rb, rfl, hc⟩ := hv
    rcases hc with ⟨htier, x, s, B, h1, -, h3, rfl, -, -, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · simp only [pp, htier, if_true, h1, hbx _ _ h3] at hp
      by_cases hlt : B.tag - s < (armsOf Ra).length
      · simp only [hlt, if_true] at hp
        by_cases hbr : isBoxed Ra = true
        · simp only [hbr, if_true] at hp
          exact iha PT ρ η _ ws i hbx hPT ((hA hlt).1 hbr) hp
        · simp [hbr] at hp
      · simp only [hlt, if_false] at hp
        by_cases hbr : isBoxed Rb = true
        · simp only [hbr, if_true] at hp
          exact ihb PT ρ η _ ws i hbx hPT ((hB (by omega)).1 hbr) hp
        · simp [hbr] at hp
    · have htb : (Ty.sum Ra Rb).tier ≠ .boxed := by
        intro h; rw [h] at hd; simp [decodeArm] at hd
      simp only [pp, htb, if_false, hd] at hp
      by_cases hp0 : p = []
      · simp [hp0] at hp
      simp only [hp0, if_false] at hp
      by_cases hj : j < (armsOf Ra).length
      · simp only [hj, if_true] at hp
        obtain ⟨q, hq, hvq⟩ := hA hj
        simp only [hq] at hp
        have hf := iha PT ρ η _ q _ hbx hPT hvq hp
        intro w a' g hw hv'
        obtain ⟨w', g', hw', hv1, he1⟩ := dec_corr hd hp0 i w a' g hw hv'
        obtain ⟨w'', g'', hw'', hv2, he2⟩ := ofArm_corr hq _ w' a' g' hw' hv1
        obtain ⟨f, hf1, hf2⟩ := hf w'' a' g'' hw'' hv2
        exact ⟨f, hf1, by rw [he2, he1] at hf2; exact hf2⟩
      · simp only [hj, if_false] at hp
        obtain ⟨q, hq, hvq⟩ := hB (by omega)
        simp only [hq] at hp
        have hf := ihb PT ρ η _ q _ hbx hPT hvq hp
        intro w a' g hw hv'
        obtain ⟨w', g', hw', hv1, he1⟩ := dec_corr hd hp0 i w a' g hw hv'
        obtain ⟨w'', g'', hw'', hv2, he2⟩ := ofArm_corr hq _ w' a' g' hw' hv1
        obtain ⟨f, hf1, hf2⟩ := hf w'' a' g'' hw'' hv2
        exact ⟨f, hf1, by rw [he2, he1] at hf2; exact hf2⟩
  | _ => intro PT ρ η rt ws i _ _ _ hp; simp [pp] at hp

/-- **W `VR` at a `PubPos` position is fresh** (replaces `VR_pubTopFresh` in `VR_VRb2`). -/
theorem VR_PubPosFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hR : RelsSound η)
    (hp : PubPos η t rt ws = true) (h : VR ρ η t rt ws) : FreshW η ws := by
  refine FreshW_of_at0 (VR_ppFresh η.box t (PTop η) ρ η rt ws 0 (fun _ _ h => h) ?_ h hp)
  intro k rt' ws' i hq w0 h0 hr
  have hv := VR_up (η.wit k) rt' w0 ws' h0 (hR.1 k rt' w0 hr)
  exact VR_ppFresh η.box (η.wit k) (fun _ _ _ _ => false) (fun _ => 0) (CE η) rt' ws' i
    (fun _ _ h => h) (fun _ _ _ _ h => by simp at h) hv hq

/-- (P2 producer) **W `VR` at a `PubPosE` position is fresh**: `VR_ppFresh` is generic over any
`bx ⊇ η.box` (its only box read is the boxed-sum arm, where `VR` supplies `η.box x = some B`); RelsSound feeds the
tvar oracle exactly as in `VR_PubPosFresh`.  This replaces the planned `pp_boxExt` equality (not needed). -/
theorem VR_PubPosEFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hR : RelsSound η)
    (hp : PubPosE η t rt ws) (h : VR ρ η t rt ws) : FreshW η ws := by
  obtain ⟨bx, hbx, hp⟩ := hp
  refine FreshW_of_at0 (VR_ppFresh bx t (PTopB bx η) ρ η rt ws 0 hbx ?_ h hp)
  intro k rt' ws' i hq w0 h0 hr
  have hv := VR_up (η.wit k) rt' w0 ws' h0 (hR.1 k rt' w0 hr)
  exact VR_ppFresh bx (η.wit k) (fun _ _ _ _ => false) (fun _ => 0) (CE η) rt' ws' i
    hbx (fun _ _ _ _ h => by simp at h) hv hq

theorem VR_VRb2 (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (bk : Prop) (rt : Shp) (ws : List Word),
    RelsSound η → VR ρ η t rt ws → VRb2 ρ η bk t rt ws := by
  induction t with
  | tid =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨l, c, h1, h2, h3, hm⟩ := h; exact ⟨l, c, h1, h2, h3, ModeOK_b _ hm⟩
  | refine t ψ ih =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    exact ⟨ih _ _ _ _ _ hR h.1, h.2, fun hp => Or.inl (VR_PubPosEFresh hR hp h.1)⟩
  | iex b ih =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ hR hv⟩
  | prod a b iha ihb =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨ra, rb, hrt, hf⟩ := h
    exact ⟨ra, rb, hrt, fun n hn => ⟨(hf n hn).1, iha _ _ _ _ _ hR (hf n hn).2.1, ihb _ _ _ _ _ hR (hf n hn).2.2⟩⟩
  | sum a b iha ihb =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h
    refine ⟨n, Ra, Rb, hrt, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · refine Or.inl ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, fun hl => ⟨fun hb => iha _ _ _ _ _ hR ((hA hl).1 hb),
        fun hb => ?_⟩, fun hl => ⟨fun hb => ihb _ _ _ _ _ hR ((hB hl).1 hb), fun hb => ?_⟩⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hb; exact ⟨q, q1, q2, q3, q4, iha _ _ _ _ _ hR.unsee q5⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl).2 hb; exact ⟨q, q1, q2, q3, q4, ihb _ _ _ _ _ hR.unsee q5⟩
    · refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj; exact ⟨q, q1, iha _ _ _ _ _ hR q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj; exact ⟨q, q1, ihb _ _ _ _ _ hR q2⟩
  | ptr μ u _ =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨a, c, h1, h2, h3, h4, hm, h5⟩ := h; exact ⟨a, c, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩
  | ptrOpt μ u _ =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    rcases h with h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩
  | loc μ u _ =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    rcases h with h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩
  | tex κ b ih =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ (hR.push0 s) hv⟩
  | mu b ih =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    exact ih _ _ _ _ _ (hR.push0 _) h
  | iall b ih =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    exact fun n => ih _ _ _ _ _ hR (h n)
  | tvar k =>
    intro ρ η bk rt ws hR h; simp only [VR] at h; simp only [VRb2]
    obtain ⟨ws', h1, h2⟩ := h; exact ⟨ws', h1, Or.inl h2⟩
  | _ =>
    intro ρ η bk rt ws hR h
    (try simp only [VR] at h) <;> (try simp only [VRb2]) <;> exact h


theorem VR_VRB {ρ η t rt ws} (hR : RelsSound η) (h : VR ρ η t rt ws) : VRB ρ η t rt ws := VR_VRb2 t ρ η False rt ws hR h

end TermSound.Flat
