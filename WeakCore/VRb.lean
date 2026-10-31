import WeakCore.TermStep
/-! The original relation `VRb` (P1/P2).  Route (iii): `ModeOKb` exempts a pub word whose range is
backed by `rc` (flag `bk`); `VRb` is `VR` (TermSound:1412–1481, generated from it) with
`ModeOK` swapped and `bk` threaded: set by a refinement `ini k` with `k ≤ rc` (`IniRc`) for
pointers, by `IniAt rc` at the offset for locatives; reset where the words change. -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

def ModeOKb (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) (bk : Prop) :
    Mode → WeakMem.AllocLabel → Cell → List Word → Prop
  | .own, _, c, _ => c.owner = some i
  | .pub, l, c, ws => ∃ f, P l = some f ∧ (S l ∨ (∀ w ∈ ws, f ≤ w.view) ∨ (c.owner = some i ∧ bk))
  | .rgn _, _, _, _ => True

/-- A refinement's count is backed by `rc` (positive reading; `False` off `.ini`). -/
def IniRc (ρ : Nat → Nat) (rc : WeakMem.AllocLabel → Nat) : Pred → List Word → Prop
  | .ini k, ws => ∃ a : WeakMem.Address, ws.map (·.val) = [.loc a 0] ∧ ev ρ k ≤ rc a.label
  | .and p q, ws => IniRc ρ rc p ws ∨ IniRc ρ rc q ws
  | _, _ => False

theorem ModeOK_b {i P S} (bk : Prop) {μ l c ws} (h : ModeOK i P S μ l c ws) : ModeOKb i P S bk μ l c ws := by
  cases μ with
  | own => exact h
  | pub => obtain ⟨f, hf, h⟩ := h; exact ⟨f, hf, h.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  | rgn _ => trivial

def VRb (ρ : Nat → Nat) (η : TEnv) : Prop → Ty → Shp → List Word → Prop
  | _bk, .intS i, _, ws => ws.map (·.val) = [.num (ev ρ i)]
  | _bk, .int, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | _bk, .opq _, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | _bk, .tid, _, ws => ∃ l c, ws.map (·.val) = [.loc ⟨l, 0⟩ 0] ∧ η.sto l = some c ∧ c.ty = .unit ∧
      ModeOKb η.tid η.pfr η.seen False .pub l c ws
  | _bk, .fix sg w, rt, ws => rt = .fix sg w ∧ ∃ n, ws.map (·.val) = [.num n] ∧ n < pw2 w
  | _bk, .lanes sg w, rt, ws => rt = .lanes sg w ∧ ∃ n, ws.map (·.val) = [.num n]
  | bk, .refine t ψ, rt, ws => VRb ρ η (bk ∨ IniRc ρ η.rc ψ ws) t rt ws ∧ IniR ρ (η.selIni t) ψ ws
  | bk, .iex b, rt, ws => ∃ n rb w, rt = .iex n rb ∧ VRb (vcons w ρ) η bk b rb ws
  | _bk, .prod a b, rt, ws => ∃ ra rb, rt = .prod ra rb ∧ ∀ n, ra.wc = some n →
      n ≤ ws.length ∧ VRb ρ η False a ra (ws.take n) ∧ VRb ρ η False b rb (ws.drop n)
  -- T3c-5d: a boxed sum is a reference to a box whose payload, re-injected into
  -- the summand its tag (less the offset `s`) selects, is a value there; a boxed
  -- summand is read through the same reference, its tag offset further (`vsh`)
  | _bk, .sum a b, rt, ws => ∃ n Ra Rb, rt = .sum n (.sum Ra Rb) ∧
      (((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x s B, ws.map (·.val) = [.loc x 0] ∧ x.offset = 0 ∧
          η.box x.label = some B ∧ n = some (s + 1) ∧
          (s ≤ B.tag ∧ ((armsOf (.sum Ra Rb))[B.tag - s]?).bind wc = some B.pay.length) ∧
          ((η.seen x.label ∧ ∃ f, η.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) ∧
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VRb ρ η False a (vsh s (shp Ra)) ws) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) B.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VRb ρ η.unsee False a (shp Ra) q)) ∧
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VRb ρ η False b (vsh (s + (armsOf Ra).length) (shp Rb)) ws) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VRb ρ η.unsee False b (shp Rb) q))) ∨ ∃ j p,
        decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws = some (j, p) ∧
        (j < (armsOf Ra).length → ∃ q, ofArm Ra j p = some q ∧ VRb ρ η False a (shp Ra) q) ∧
        ((armsOf Ra).length ≤ j → ∃ q, ofArm Rb (j - (armsOf Ra).length) p = some q ∧ VRb ρ η False b (shp Rb) q))
  | _bk, .tvar k, rt, ws => ∃ ws', WLe ws' ws ∧ η.get k rt ws'
  | _bk, .code σ τ _, rt, ws => ∃ i d, ws.map (·.val) = [.num i] ∧ η.prog[i]? = some d ∧
      η.prog.find? (·.name == d.name) = some d ∧ d.tparams = [] ∧ d.idx = [] ∧
      cl ρ η.wit 0 0 σ = clD d.argTy ∧ cl ρ η.wit 0 0 τ = clD d.retTy
  -- T3c-3: a reference's cell is in Σ, holds exactly the closure of the target
  -- type (invariant: no strong update), and agrees with the mode
  | bk, .ptr μ u, _, ws => ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
      Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen bk μ a.label c ws ∧ accs c.ty ≠ none
  -- F5: `null` is a locative only to a zero-length array (`zeroableIn`), which
  -- no access reaches (T3c-5a)
  | bk, .loc μ u, _, ws => (ws.map (·.val) = [.null] ∧ ∃ e, Fd (.array (.lit 0) e) (cl ρ η.wit 0 0 u)) ∨
      ∃ a c U, ws.map (·.val) = [.loc a 0] ∧ η.sto a.label = some c ∧
        AtOff c.ty a.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen (bk ∨ IniAt η.rc c a U) μ a.label c ws ∧
          IniAt (modeIni μ η.ini η.rini) c a U
  | bk, .ptrOpt μ u, _, ws => ws.map (·.val) = [.null] ∨
      ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
        Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOKb η.tid η.pfr η.seen bk μ a.label c ws ∧ accs c.ty ≠ none
  | _bk, .void, _, _ => False
  -- T3c: some closed witness `s`; its variable has no values (`push0`), which
  -- `guardT` keeps where `VR` reads only witnesses (code signatures, and from
  -- T3c-3 reference targets)
  | bk, .tex κ b, rt, ws => ∃ n rb s, rt = .tex n rb ∧ Clo s ∧ WitOK κ s ∧ VRb ρ (η.push0 s) bk b rb ws
  -- T3c-5a: the body, its variable the closed `μ` type itself; the
  -- variable is guarded (`guardT`), so its (empty, `push0`) relation is never
  -- read, and `VR` at a reference to it compares with the witness
  | bk, .mu b, rt, ws => VRb ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) bk b rt ws
  -- T3c-5f: indices are erased, so a value of `∀i. b` is, on the same words, a
  -- value of `b` at every index
  | bk, .iall b, rt, ws => ∀ n, VRb (vcons n ρ) η bk b rt ws
  -- T3d-1: a protocol word's protocol is well formed (`mkWord` checks it), and a
  -- runtime word holds a state of it
  | _bk, .word _ P, _, ws => pwf P = true ∧ (P.ghost = false → ∃ n, ws.map (·.val) = [.num n] ∧ InP P n)
  -- T3d-1: a protocol pair holds a pair state (`mkWord2`, `stp` and `casp`
  -- check one); an epoch pair holds two numbers (`caspE` writes the live
  -- token's epoch and an arbitrary value, so nothing stronger is invariant)
  | _bk, .word2 _ P, _, ws => pwf2 P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] ∧ InP2 P n0 n1
  | _bk, .epair _ P, _, ws => pwfE P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1]
  | _bk, _, _, _ => True


end TermSound.Flat
