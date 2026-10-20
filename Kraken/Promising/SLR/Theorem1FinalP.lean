/-
Theorem 1′ at the fence-aware guards and option (S)'s frame (from
`SLR/NPSafePInst.lean`, now against the existing generic chain).

- `theorem1IIPure_F_S`: `Theorem1IIPure'` at the fence-aware guard `GF`
  (prepay and virtual guard) and the frame `K2Scope (model I) AllocIds`.
- `theorem1IIPure_Hyb_S`: the same at the impure-only fence-aware guard
  `GHyb rel`.
- `PromisePure'.mono`: `PromisePure'` is antitone in the guard, so the
  existing `PromisePure` proofs (at `G₀`) transfer (`promisePure_GF`,
  `promisePure_GHyb`).

What a program must still supply at `GF`/`GHyb` is `NPSafeP` at that guard
for every thread (`SLR/NPSafePHyb.lean` for `GHyb`).
-/
import Kraken.Promising.SLR.Theorem1Final
import Kraken.Promising.SLR.NPSafePInst
import Kraken.Promising.SLR.NPSafePFence

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- The existing `PromisePure` is `PromisePure'` at `G₀`. -/
theorem promisePure_iff_G₀ [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} :
    PromisePure A fuel states initMem rel ↔ PromisePure' G₀ A fuel states initMem rel :=
  Iff.rfl

/-- Theorem 1′ with the fence-aware guard and option (S)'s frame together. -/
theorem theorem1IIPure_F_S [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPure' (I := I) GF GF (K2Scope (model I) AllocIds) A fuel :=
  theorem1IIPure' guardOK_GF guardOK_GF (fun _ _ _ _ _ h => h) k2OK_allocIds A fuel

/-- Theorem 1′ with the impure-only fence-aware guard and option (S)'s frame. -/
theorem theorem1IIPure_Hyb_S [I.LawfulState] (rel : Loc → Pred) (A : Arch) (fuel : Nat) :
    Theorem1IIPure' (I := I) (GHyb rel) (GHyb rel) (K2Scope (model I) AllocIds) A fuel :=
  theorem1IIPure' (guardOK_GHyb rel) (guardOK_GHyb rel) (fun _ _ _ _ _ h => h) k2OK_allocIds A fuel

/-- `PromisePure'` is antitone in the guard: a wider guard sends more promises
to (d1), so fewer need to be pure. -/
theorem PromisePure'.mono [I.LawfulState] {G G' : PrepayGuard I}
    (hG : ∀ A tid ts t mem, G A tid ts t mem → G' A tid ts t mem)
    {A : Arch} {fuel : Nat} {states : List I.State} {initMem : List (Loc × Val)} {rel : Loc → Pred}
    (h : PromisePure' G A fuel states initMem rel) : PromisePure' G' A fuel states initMem rel :=
  fun π h0 hf J hJ j t pw ht hw hJ1 hn => h π h0 hf J hJ j t pw ht hw hJ1 fun ⟨f, h1, h2, h3, tf, tf', h4, h5, h6, h7⟩ =>
    hn ⟨f, h1, h2, h3, tf, tf', h4, hG _ _ _ _ _ h5, h6, h7⟩

/-- Existing (`G₀`) `PromisePure` proofs transfer to `GF`. -/
theorem promisePure_GF [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State} {initMem : List (Loc × Val)}
    {rel : Loc → Pred} (h : PromisePure A fuel states initMem rel) : PromisePure' GF A fuel states initMem rel :=
  PromisePure'.mono (fun _ _ _ _ _ h => G₀_le_GF h) h

/-- Existing (`G₀`) `PromisePure` proofs transfer to `GHyb rel'`. -/
theorem promisePure_GHyb [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State} {initMem : List (Loc × Val)}
    {rel rel' : Loc → Pred} (h : PromisePure A fuel states initMem rel) :
    PromisePure' (GHyb rel') A fuel states initMem rel :=
  PromisePure'.mono (fun _ _ _ _ _ h => G₀_le_GHyb rel' h) h

end Kraken.Promising.SLR
