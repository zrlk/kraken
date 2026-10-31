import WeakCore.WrIniInst
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-- The merge on values: a reference into `l'` becomes one into `l` (same offset and tag). -/
def lrv (l' l : WeakMem.AllocLabel) : WeakMem.Val → WeakMem.Val
  | .loc a g => if a.label = l' then .loc ⟨l, a.offset⟩ g else .loc a g
  | v => v

def lr (l' l : WeakMem.AllocLabel) (w : Word) : Word := { w with val := lrv l' l w.val }

/-- The merge hypotheses: `η₁` (W, the K query env) is `η₂` (♭, the original) plus the fresh copy `l'` of `l`. -/
structure MergeOK (l' l : WeakMem.AllocLabel) (η₁ η₂ : TEnv) : Prop where
  ne : l' ≠ l
  wit : η₁.wit = η₂.wit
  prog : η₁.prog = η₂.prog
  tid : η₁.tid = η₂.tid
  sto : ∀ m c, m ≠ l' → η₁.sto m = some c → η₂.sto m = some c
  ini : ∀ m, m ≠ l' → η₁.ini m ≤ η₂.ini m
  rini : ∀ m, m ≠ l' → η₁.rini m ≤ η₂.rini m
  pfr : ∀ m f, m ≠ l' → η₁.pfr m = some f → η₂.pfr m = some f
  seen : ∀ m, m ≠ l' → η₁.seen m → η₂.seen m
  box : ∀ m B, m ≠ l' → η₁.box m = some B → η₂.box m = some B
  -- the copy
  cl : ∃ c c', η₂.sto l = some c ∧ η₁.sto l' = some c' ∧ c'.ty = c.ty ∧ c'.owner = none ∧
    c.owner = some η₂.tid      -- (5) unit clause dropped: ♭ tid flag
  inil : η₁.ini l' ≤ η₂.rc l
  rinil : η₁.rini l' ≤ η₂.rc l
  pfrl : ∃ f, η₂.pfr l = some f
  seenl : ¬ η₁.seen l'
  boxl : η₁.box l' = none
  -- words elsewhere in η₁ (boxes) never mention `l'`: the payloads are read unrenamed
  boxfree : ∀ m B w a g, η₁.box m = some B → w ∈ B.pay → w.val = .loc a g → a.label ≠ l'

/-- **VRR_merge** (statement under review): W typing at the query env ⇒ ♭ typing at the original env,
of the merged words, with the same resource. `hr`/`hur`: the frame relations merge (at CE envs
both sides are empty; at the top level `CohR`/`CohRB` re-read them by a second instance of this lemma). -/
def VRRMergeStmt : Prop :=
  ∀ (l' l : WeakMem.AllocLabel) (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (X : Res),
    MergeOK l' l η₁ η₂ →
    (∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S (vs.map (lr l' l)) Y) →
    (∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S (vs.map (lr l' l)) Y) →
    VRR ρ η₁ t rt ws X → VRRB ρ η₂ t rt (ws.map (lr l' l)) X

end TermSound.Flat
