/-
**`hello1`'s landings' open premises, the program facts** (AArch64): the
facts of `H1OpenA` (`Spike/Lib/LowerA64/H1InLandA.lean`) that are about
`hello1o`'s source alone, decided over its compiled blocks.

- `hello1_hTnA`: every allocation of every compiled block of `hello1o` has
  an element type taking a word (`elem2`), at the blocks in range
  (`H1OpenA.hTn`'s guarded shape, at `T j := TailAt2 hello1o j`);
- `AbH`, `hAb_AbH`: the landing contexts' aborts gathered (`CxOkH`'s `AbU2`
  at some context, `GA`), the fragment `H1OpenA.hAb` asks the contexts'
  aborts inside, by construction;
- `h1OpenA_hello1`: `H1OpenA` at `hello1o` from `H1RestA` (`hTn` by
  `hello1_hTnA`, `hAb` by construction).
-/
import Spike.Test.A64Hello1HsOf
import Spike.Test.A64Hello1CxOkH
import Spike.Lib.LowerA64.H1RestA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.LowerNode (compiled2 TailAt2)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- **`hello1o`'s allocations take a word per element** at every compiled
block in range (`tailsL` of each block's body decided, as
`hello1_rodata_elem2` at every block). -/
theorem hello1_hTnA : ∀ j d, (compiled2 P1A)[j]? = some d →
    ∀ x cn τ e, TailAt2 P1A j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true := by
  have hc : ∀ d ∈ compiled2 P1A, (tailsL d.body).all (fun t => match t with
      | .let_ _ (.newBuf _ τ) _ => Scc.Lower.elem2 τ
      | _ => true) = true := by
    decide
  intro j d hd x cn τ e ht
  simpa using List.all_eq_true.mp (hc d (List.mem_of_getElem? hd)) _ (tailOf_mem_tailsL (ht d hd))

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

/-- **The landing contexts' aborts** (`H1OpenA`'s `Ab₀` at `CxOkH`): the
aborts of some context `CxOkH` carries (`GA`). -/
abbrev AbH (hp : Scc.Lower.Accepted2 p = true) : FragS isaLSE2 := GA (CxOkH h hp)

/-- **`H1OpenA.hAb` at `CxOkH` and `AbH`**: each context's aborts are
`AbH`'s, by construction. -/
theorem hAb_AbH (hp : Scc.Lower.Accepted2 p = true) :
    ∀ j R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → AbH h hp s c fs' :=
  fun j R F fs fp ra tp G0 Ab hc _ _ _ hA => ⟨j, R, F, fs, fp, ra, tp, G0, Ab, hc, hA⟩

/-- **`hello1`'s landings' `H1OpenA` from the rest** (`H1RestA.toOpen` at
`hello1_hTnA`; `hAb` by construction). -/
theorem h1OpenA_hello1 (h : placeOKAt pcfg (lay2 Λ P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg P1A)) = true)
    (hp : Scc.Lower.Accepted2 P1A = true) {E : Entry} {Dt : State → Prop}
    (H : H1RestA h E (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h) Dt) :
    H1OpenA h E (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h) Dt (AbH h hp) :=
  H1RestA.toOpen h H hello1_hTnA

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_hTnA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hTnA

/-- info: 'Spike.Lib.LowerA64.hAb_AbH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hAb_AbH

/-- info: 'Spike.Lib.LowerA64.h1OpenA_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.h1OpenA_hello1
