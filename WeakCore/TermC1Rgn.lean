import WeakCore.TermStep
import WeakCore.TermC1Inv

/-! # TermC1Rgn: `region` and `intoRgn` as `publish`

Opening a region publishes its cell, live or dead binder: the runtime step is `publish`'s release fence
(`fenceS .st`, TermRun L1128 / L692–705), and Σ plants the cell's frontier at `vWr` (or keeps an
already planted one) and marks it seen (`pubP`, `pubS`), exactly as `tstepM_publish`.

Stated against today's `MemInv`/`FInv`; the new facts are hypotheses:
* `hcpl`: the payload is `coupledOKIn` (checkW1's region / intoRgn test, `rgnPay`);
* `hsc : PubScope cx a`: the payload is `rgnFree` (today's `PubCpl` conjunct; at the switch `drf1`);
* `hwin`: `NoHold` at the cell (`PubWinTN1e.rgn` / `PubWinTN1e.into`);
* `hPb`: the plant gate `g.pf` at the cell.

New here:
* `PubWinTN1e`: `PubWinTN1` without its live-binder guard. Every region publishes, so the
  certification-window assumption covers every region, dead binders included.
* `RgnPubT1`: the region's cell is published and seen afterwards, from which the fresh region
  reference satisfies `ModeOK1 .rgn` (immediate: the cell is seen).
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `PubWinTN` at the three fencing operations: `publish`; every `region`, live or dead binder,
since every region publishes its cell; `intoRgn`: the cell it moves in. Unseen cells only. -/
def PubWinTN1e (E : TEnv) (s : St) (th : TTh) : Prop :=
  (∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label) ∧
  (∀ a r pn tn e rt ws ad, th.term = .region a r pn tn e →
    evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label) ∧
  (∀ x r a e rt ws ad, th.term = .let_ x (.intoRgn r a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label)

/-- `PubWinTN1e` is `PubWinTN` (M1). -/
theorem PubWinTN1e.pub {E : TEnv} {s : St} {th : TTh} (h : PubWinTN1e E s th) : TermTyped.PubWinTN E s th :=
  h

/-- `PubWinTN1e` implies `PubWinTN1` (it drops the live-binder guard). -/
theorem PubWinTN1e.toN1 {E : TEnv} {s : St} {th : TTh} (h : PubWinTN1e E s th) : PubWinTN1 E s th :=
  ⟨h.1, fun a r pn tn e rt ws ad ht _ => h.2.1 a r pn tn e rt ws ad ht, h.2.2⟩

/-- The region conjunct at a `region` term: `NoHold` at an unseen cell, any binder. -/
theorem PubWinTN1e.rgn {E : TEnv} {s : St} {th : TTh} {a : At} {r pn tn : String} {e : Expr}
    (h : PubWinTN1e E s th) (ht : th.term = .region a r pn tn e) :
    ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label →
      NoHold E s ad.label :=
  fun rt ws ad => h.2.1 a r pn tn e rt ws ad ht

/-- The `intoRgn` conjunct at an `intoRgn` term: `NoHold` at an unseen cell. -/
theorem PubWinTN1e.into {E : TEnv} {s : St} {th : TTh} {x r : String} {a : At} {e : Expr}
    (h : PubWinTN1e E s th) (ht : th.term = .let_ x (.intoRgn r a) e) :
    ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label →
      NoHold E s ad.label :=
  fun rt ws ad => h.2.2 x r a e rt ws ad ht

/-- A published, seen cell satisfies `ModeOK1 .rgn` at any words. -/
theorem ModeOK1_rgn_seen {i : Nat} {P : AllocLabel → Option Ts} {S : AllocLabel → Prop} {r : Idx}
    {l : AllocLabel} {c : Cell} {ws : List Word} (hP : P l ≠ none) (hS : S l) : ModeOK1 i P S (.rgn r) l c ws := by
  cases h : P l with
  | none => exact absurd h hP
  | some f => exact ⟨f, h, Or.inl hS⟩

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}


end

end TermC1

#print axioms TermC1.PubWinTN1e.pub
#print axioms TermC1.PubWinTN1e.toN1
#print axioms TermC1.PubWinTN1e.rgn
#print axioms TermC1.PubWinTN1e.into
#print axioms TermC1.ThInvMFR1.toF
#print axioms TermC1.ModeOK1_rgn_seen
#print axioms TermC1.RgnPubT1.of
#print axioms TermC1.IntoPubT1.of
#print axioms TermC1.pwLab
#print axioms TermC1.pubStep1
#print axioms TermC1.tstepM_region1
#print axioms TermC1.ThInvMFI1.toF
#print axioms TermC1.tstepM_intoRgn1
