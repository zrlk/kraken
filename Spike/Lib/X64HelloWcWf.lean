/-
**hello.w's `wc_main` before the spawn: the sites off its pcs** (x86-64; twin of the site lemmas of
`Spike/Lib/A64HelloWcWf.lean`, the hello twin of `Spike/Lib/X64WakeWcWf.lean` at `helloCells`). The node and block
obligations inside `WakeWf.Wf` are `X64HelloWcWfX`'s, at any owned words (the root takes `ownGHXW`).

Wake's `frameRun_hold`, `RunWf.hold`, `PlacedSE.hold` (`X64WakeWcWf`) are program independent and reused as is.

- `htk_of_freeNH`, `habt_of_okPcOfH`: a free pc is off the take site, a pc `okPcOf` is off the abort sites.

## Differences from the AArch64 version

- The pcs are byte addresses (`Int64`, `freeNH` over `toBitVec.toNat`); the sites are `PhRec.μ L`'s.
-/
import Spike.Lib.X64HelloStartWf
import Spike.Lib.X64WakeWcWf

namespace Spike.Lib.X64.HelloPh.WcWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open Scc.Cert.Rt.X64 (okPcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.WcW (freeNH site_ne_of_freeNH)

section Gen

variable {L : RuntimeLayout}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

include hsite hlab in
/-- **A free pc is off the take site.** -/
theorem htk_of_freeNH {pc : Int64} (hf : freeNH pc.toBitVec.toNat = true) :
    ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite] at hx; cases hx; exact site_ne_of_freeNH hlab hf

include hp hlo in
/-- **A pc `okPcOf` is off the abort sites.** -/
theorem habt_of_okPcOfH {pc : Int64} (hok : okPcOf lo helloCells L.Λ pc.toBitVec.toNat = true) :
    ∀ k x, (Spike.Lib.X64.PhRec.μ L).abortAt k = some x → pc.toBitVec.toNat ≠ x := fun j _ hx =>
  Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hok) (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx

end Gen

end Spike.Lib.X64.HelloPh.WcWf

/-! ## Axioms -/

/--
info: 'Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH
