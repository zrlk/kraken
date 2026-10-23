import WeakCore.TermDPlus

/-! # TermC1Win: the seen half of the region certification window (G7)

`TermDPlus.noHoldPubA_of_N` discharges a *seen* `publish` from `MemInv`: the published label is an own
cell of the store (`TermPubSto.pubSto_of_typed`), so `noHold_seen` applies.  Under c1 `region` and
`intoRgn` publish too (`TermC1Rgn.PubWinTN1e`, unseen cells only); this module is their seen half:

* `rgnSto_of_typed` / `intoSto_of_typed`: the handles a typed `region` / `intoRgn` consumes
  name own cells of the store (`TermPubSto.ownSto_of_use` / `ownBufSto_of_use`; the missing
  `pubSto_of_typed` analogue);
* `rgn_noHold_seen` / `into_noHold_seen`: at a seen cell, `NoHold` from `MemInv`.

Only the typing, `FInv` and (for `NoHold`) `MemInv` at the current typing are used.  No definition is
added; the certificate-side run fact over `PubWinTN1e` is switch-gate work.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermTyped
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {a : At} {rt : Ty} {ws : List Word}
  {ad : Address}

/-- **A typed `region` names an own cell of the store** (`TermPubSto.pubSto_of_typed` for `region`). -/
theorem rgnSto_of_typed {rn pn tn : String} {e : Expr} (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hterm : th.term = .region a rn pn tn e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) :
    ∃ c, (CE η).sto ad.label = some c ∧ c.owner = some (CE η).tid := by
  rw [hterm] at hT
  cases hT with
  | region hu _ _ _ _ => exact TermPubSto.ownSto_of_use hu hi hea hws
  | regionBuf hu _ _ _ _ => exact TermPubSto.ownBufSto_of_use hu hi hea hws

/-- **A typed `intoRgn` names an own cell of the store** (`TermPubSto.pubSto_of_typed` for `intoRgn`). -/
theorem intoSto_of_typed {x rn : String} {e : Expr} (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hterm : th.term = .let_ x (.intoRgn rn a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) :
    ∃ c, (CE η).sto ad.label = some c ∧ c.owner = some (CE η).tid := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
  cases hop with
  | intoRgn _ hu _ _ => exact TermPubSto.ownSto_of_use hu hi hea hws
  | intoRgnBuf _ hu _ _ => exact TermPubSto.ownBufSto_of_use hu hi hea hws

/-- **(G7) The seen `region`**: `NoHold` at its cell from `MemInv` (`TermDPlus.noHold_seen`). -/
theorem rgn_noHold_seen {g : G} {s : St} {rn pn tn : String} {e : Expr} (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) s)
    (hterm : th.term = .region a rn pn tn e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0])
    (hs : (CE η).seen ad.label) : NoHold (CE η) s ad.label := by
  obtain ⟨c, hc, ho⟩ := rgnSto_of_typed hT hi hterm hea hws
  exact TermDPlus.noHold_seen hm hc ho hs

/-- **(G7) The seen `intoRgn`**: `NoHold` at its cell from `MemInv` (`TermDPlus.noHold_seen`). -/
theorem into_noHold_seen {g : G} {s : St} {x rn : String} {e : Expr} (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) s)
    (hterm : th.term = .let_ x (.intoRgn rn a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0])
    (hs : (CE η).seen ad.label) : NoHold (CE η) s ad.label := by
  obtain ⟨c, hc, ho⟩ := intoSto_of_typed hT hi hterm hea hws
  exact TermDPlus.noHold_seen hm hc ho hs

end

end TermC1

#print axioms TermC1.rgnSto_of_typed
#print axioms TermC1.intoSto_of_typed
#print axioms TermC1.rgn_noHold_seen
#print axioms TermC1.into_noHold_seen
