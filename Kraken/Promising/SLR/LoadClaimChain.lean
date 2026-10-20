/-
**Design prototype.** The Theorem 1′ statement over an
**extended erasure** `Erase ∧ X` (open, as a `Prop`), and the proof that the
existing statement is its instance at `X = ⊤`.

- `modelE e`: the SLR model with erasure `e` (everything else as in
  `model I`). `modelE Erase` is `model I` definitionally (structure eta), and
  `K2Frame (modelE e)` does not depend on `e`.
- `modelX X := modelE (Erase ∧ X)`; `modelT D := modelX (TicketInv D)`.
- `PromiseFresh'`: the a-posteriori promise obligation of the extension, the
  analogue of `PromisePure'` (promises not fulfilled by a release store
  satisfy `Fresh`, here: `Dispenser.Fresh`).
- `Theorem1IIPureX' G GV K X Fresh`: `Theorem1IIPure'` with `Erase ∧ X` at
  the initial and the virtual configuration, `NPSafeP (modelX X)` for the
  threads, and `PromiseFresh'` as an extra hypothesis. **Proved** in `SLR/LoadClaimFinal.lean`: `theorem1IIPureX'` for every `X`
  with a promise law, `theorem1IIPureX'_ticket` / `theorem1IIPureT` for the
  ticket (the chain is generic in its erasure, `ChainExt`).
- `theorem1IIPure'_of_X`: `Theorem1IIPureX'` at `X = ⊤`, `Fresh = ⊤` gives the
  existing `Theorem1IIPure'`: the existing chain is the trivial instance, so a
  generic chain loses nothing.
- `theorem1IIPureT_of_X`: the ticket instance, with `EraseT` in the
  conclusion.

Nothing imports this file.
-/
import Kraken.Promising.SLR.LoadClaim
import Kraken.Promising.SLR.Theorem1Final

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- The SLR model with erasure `e`. -/
def modelE (I : ISA) (e : (Nat → Res) → Ghost → (Nat → Prop) → Config I → Prop) : ResModel I :=
  { model I with erase := e }

/-- `modelE` at `Erase` is `model I` (structure eta). -/
theorem modelE_erase : modelE I Erase = model I := rfl

/-- The SLR model with erasure `Erase ∧ X`. -/
def modelX (I : ISA) (X : Ghost → Config I → Prop) : ResModel I :=
  modelE I (fun rF g T c => Erase rF g T c ∧ X g c)

/-- The ticket model: erasure `EraseT D`. -/
def modelT (I : ISA) (D : Dispenser) : ResModel I := modelX I (fun g c => D.TicketInv g c)

theorem modelT_erase (D : Dispenser) : (modelT I D).erase = EraseT D := rfl

/-- **The extension's promise obligation** (a posteriori over real paths to a
final configuration, as `PromisePure'`): a promise that is not
`RelFulfilled'` writes a `Fresh` message. -/
def PromiseFresh' (G : PrepayGuard I) (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State)
    (initMem : List (Loc × Val)) (Fresh : Memory → Msg → Prop) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J, J < π.len → ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    ¬ RelFulfilled' G π J j ((π.cfg J).mem.last + 1) →
    Fresh (π.cfg J).mem { pw.1 with tid := j }

/-- **Theorem 1′ over the extended erasure `Erase ∧ X`** (open). -/
def Theorem1IIPureX' (G GV : PrepayGuard I) (K : K2Frame (model I)) (X : Ghost → Config I → Prop)
    (Fresh : Memory → Msg → Prop) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → X g (Config.init states initMem) →
    (∀ ts, ts ∉ g.pend) →
    PromisePure' G A fuel states initMem g.rel →
    PromiseFresh' G A fuel states initMem Fresh →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafeP (modelX I X) A B tid G K n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', c.VirtualOfG GV A v ∧ Erase rF' g' (fun _ => False) v ∧ X g' v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- `Erase ∧ True` is `Erase`. -/
theorem erase_and_true :
    (fun (rF : Nat → Res) (g : Ghost) (T : Nat → Prop) (c : Config I) => Erase rF g T c ∧ True) = Erase := by
  funext rF g T c; exact and_true _

/-- `NPSafeP` at `modelX ⊤` is `NPSafeP` at `model I`. -/
theorem npSafeP_modelX_top {A : Arch} {B : Config I → Res → Ghost → Prop} {tid : Nat} {G : PrepayGuard I}
    {K : K2Frame (model I)} {n m : Nat} {cl : Prop} {c : Config I} {r : Res} {g : Ghost} :
    NPSafeP (modelX I (fun _ _ => True)) A B tid G K n m cl c r g ↔ NPSafeP (model I) A B tid G K n m cl c r g := by
  show NPSafeP (modelE I (fun rF g T c => Erase rF g T c ∧ True)) A B tid G K n m cl c r g ↔
    NPSafeP (modelE I Erase) A B tid G K n m cl c r g
  rw [erase_and_true]

/-- **The existing Theorem 1′ is the instance `X = ⊤`, `Fresh = ⊤`** of the
extended statement. -/
theorem theorem1IIPure'_of_X [I.LawfulState] {G GV : PrepayGuard I} {K : K2Frame (model I)} {A : Arch} {fuel : Nat}
    (h : Theorem1IIPureX' G GV K (fun _ _ => True) (fun _ _ => True) A fuel) : Theorem1IIPure' G GV K A fuel := by
  intro B states initMem rF g hNT E hpend hpure hsafe c hc hlive
  obtain ⟨v, rF', g', hv, E', -, hle, hB⟩ :=
    h B states initMem rF g hNT E trivial hpend hpure (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun tid htid n m => npSafeP_modelX_top.mpr (hsafe tid htid n m)) c hc hlive
  exact ⟨v, rF', g', hv, E', hle, hB⟩

/-- **The ticket instance**: from the extended Theorem 1′, a ticket program
whose threads are `NPSafeP` at `modelT D`, whose initial ghost satisfies the
ticket invariant and whose promises are `Fresh` gets `EraseT D` at the
virtual configuration. -/
theorem theorem1IIPureT_of_X [I.LawfulState] {G GV : PrepayGuard I} {K : K2Frame (model I)} {A : Arch} {fuel : Nat}
    (D : Dispenser) (h : Theorem1IIPureX' G GV K (fun g c => D.TicketInv g c) D.Fresh A fuel)
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val)) (rF : Nat → Res)
    (g : Ghost) (hNT : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (E : EraseT D rF g (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g.pend)
    (hpure : PromisePure' G A fuel states initMem g.rel) (hfresh : PromiseFresh' G A fuel states initMem D.Fresh)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (modelT I D) A B tid G K n m True (Config.init states initMem) (rF tid) g)
    (c : Config I) (hc : Reachable A fuel (Config.init states initMem) c) (hlive : c.Live A fuel) :
    ∃ v rF' g', c.VirtualOfG GV A v ∧ EraseT D rF' g' (fun _ => False) v ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' := by
  obtain ⟨v, rF', g', hv, E', hX, hle, hB⟩ := h B states initMem rF g hNT E.1 E.2 hpend hpure hfresh hsafe c hc hlive
  exact ⟨v, rF', g', hv, ⟨E', hX⟩, hle, hB⟩

#print axioms theorem1IIPure'_of_X
#print axioms theorem1IIPureT_of_X

end Kraken.Promising.SLR
