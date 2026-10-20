import WeakCore.TermC1Defs
import WeakCore.TermPtrRtsDefs

/-! # TermC1Inv: region c1, the invariant-side definitions under new names

New definitions only, alongside the old ones; no existing definition, premise or theorem mentions them.
Each is a parallel copy of the named original with the c1 change, deleted when the change is adopted.

| new | original | change |
|---|---|---|
| `ModeOK1` | `TermSound.ModeOK` (TermSound L597) | `rgn _` takes the `pub` clause (M1) |
| `noOR1` | `TermCut.noOR` (TermCut L37) | `ptr`/`ptrOpt (rgn _)` admitted; `loc (rgn _)` stays out |
| `PubCpl1` | `TermStep.PubCpl` (TermStep L1637) | `rgnFree` → `drf1` |
| `PlantEdge1` | `TermPtrRts.PlantEdge` (TermPtrRtsDefs L21) | `rgnFree` dropped |
| `PubWinTN1` | `TermTyped.PubWinTN` (TermTyped L630) | publish ∨ live `region` (b1) ∨ `intoRgn` (h2) |
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermGlob TermTyped
open TermCut TermPtrRts TermScope
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (M1, c1) `ModeOK` with a region reference held to the `pub` clause: the cell has a frontier and
the word carries a view past it, or the thread has seen the cell. -/
def ModeOK1 (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) :
    Mode → WeakMem.AllocLabel → Cell → List Word → Prop
  | .own, _, c, _ => c.owner = some i
  | .pub, l, _, ws => ∃ f, P l = some f ∧ (S l ∨ ∀ w ∈ ws, f ≤ w.view)
  | .rgn _, l, _, ws => ∃ f, P l = some f ∧ (S l ∨ ∀ w ∈ ws, f ≤ w.view)

/-- (S7e, c1) `noOR` with region pointers admitted (they carry views, `ModeOK1`); `loc (rgn _)` stays
out. -/
def noOR1 : Ty → Bool
  | .ptr .pub _    => true
  | .ptr (.rgn _) _ => true
  | .ptr _ _       => false
  | .ptrOpt .pub _ => true
  | .ptrOpt (.rgn _) _ => true
  | .ptrOpt _ _    => false
  | .loc .pub _    => true
  | .loc _ _       => false
  | .prod a b      => noOR1 a && noOR1 b
  | .sum a b       => noOR1 a && noOR1 b
  | .array _ t     => noOR1 t
  | .mu t          => noOR1 t
  | .tex _ t       => noOR1 t
  | .iall t        => noOR1 t
  | .iex t         => noOR1 t
  | .refine t _    => noOR1 t
  | _              => true

/-- (M5b, c1) `PubCpl` with `rgnFree` replaced by `drf1`: region cells are published cells. -/
def PubCpl1 (E : TEnv) : Prop :=
  ∀ l c f, E.sto l = some c → E.pfr l = some f →
    LayT c.ty ∧ (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
      Ty.noOwnIn [] c.ty = true ∧ drf1 c.ty = true

/-- (c1) `PlantEdge` without `rgnFree`: message `m` sits at a noOwn cell of `sto` and names label `a`. -/
def PlantEdge1 (sto : Sto) (m : Msg) (a : AllocLabel) : Prop :=
  (∃ ca, sto m.loc.label = some ca ∧ Ty.noOwnIn [] ca.ty = true) ∧
  ∃ (a' : Address) (g : Nat), m.val = .loc a' g ∧ a'.label = a

/-- (D+, c1) `PubWinTN` at the three fencing operations: `publish`, a live `region` (b1), and `intoRgn`
(h2). -/
def PubWinTN1 (E : TEnv) (s : St) (th : TTh) : Prop :=
  (∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label) ∧
  (∀ a r pn tn e rt ws ad, th.term = .region a r pn tn e → freeB pn e = true →
    evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label) ∧
  (∀ x r a e rt ws ad, th.term = .let_ x (.intoRgn r a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label)

/-- The publish conjunct of `PubWinTN1` is `PubWinTN`. -/
theorem PubWinTN1.pub {E : TEnv} {s : St} {th : TTh} (h : PubWinTN1 E s th) : PubWinTN E s th := h.1

/-- `noOR` implies `noOR1` (c1 only admits more). -/
theorem noOR1_of_noOR : ∀ {t : Ty}, noOR t = true → noOR1 t = true
  | .ptr μ u, h => by cases μ <;> simp_all [noOR, noOR1]
  | .ptrOpt μ u, h => by cases μ <;> simp_all [noOR, noOR1]
  | .loc μ u, h => by cases μ <;> simp_all [noOR, noOR1]
  | .prod a b, h => by
      simp only [noOR, Bool.and_eq_true] at h
      simp only [noOR1, Bool.and_eq_true]
      exact ⟨noOR1_of_noOR h.1, noOR1_of_noOR h.2⟩
  | .sum a b, h => by
      simp only [noOR, Bool.and_eq_true] at h
      simp only [noOR1, Bool.and_eq_true]
      exact ⟨noOR1_of_noOR h.1, noOR1_of_noOR h.2⟩
  | .array _ t, h => by simp only [noOR] at h; simp only [noOR1]; exact noOR1_of_noOR h
  | .mu t, h => by simp only [noOR] at h; simp only [noOR1]; exact noOR1_of_noOR h
  | .tex _ t, h => by simp only [noOR] at h; simp only [noOR1]; exact noOR1_of_noOR h
  | .iall t, h => by simp only [noOR] at h; simp only [noOR1]; exact noOR1_of_noOR h
  | .iex t, h => by simp only [noOR] at h; simp only [noOR1]; exact noOR1_of_noOR h
  | .refine t _, h => by simp only [noOR] at h; simp only [noOR1]; exact noOR1_of_noOR h
  | .unit, _ | .void, _ | .int, _ | .intS _, _ | .fix _ _, _ | .lanes _ _, _ | .code _ _, _
  | .share _, _ | .cap _ _, _ | .word _ _, _ | .tok _ _, _ | .word2 _ _, _ | .tok2 _ _ _ _, _
  | .epair _ _, _ | .tokE _ _ _, _ | .tvar _, _ => by simp [noOR1]

/-- `PlantEdge` implies `PlantEdge1`. -/
theorem PlantEdge1_of_PlantEdge {sto : Sto} {m : Msg} {a : AllocLabel} (h : PlantEdge sto m a) :
    PlantEdge1 sto m a :=
  ⟨let ⟨ca, h1, h2, _⟩ := h.1; ⟨ca, h1, h2⟩, h.2⟩

/-- `ModeOK1` agrees with `ModeOK` off region modes. -/
theorem ModeOK1_pub (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) :
    ModeOK1 i P S .pub = ModeOK i P S .pub := rfl
theorem ModeOK1_own (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) :
    ModeOK1 i P S .own = ModeOK i P S .own := rfl

end TermC1

#print axioms TermC1.PubWinTN1.pub
#print axioms TermC1.noOR1_of_noOR
#print axioms TermC1.PlantEdge1_of_PlantEdge
#print axioms TermC1.ModeOK1_pub
#print axioms TermC1.ModeOK1_own
