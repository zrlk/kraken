/-
**The first TCB's limit word is mapped** (x86-64; the twin of
`Spike/Lib/LowerA64/G1Hmr.lean`): the stack check's limit word `limA tp`
at the first TCB's thread pointer is mapped for reading in the loaded
kernel state `K0`, the premise `hmr` of the prologue lemmas (`proW_w2C`,
`proW_w2F`), from the runtime layout's words
(`RuntimeLayout.words_mapped`: the limit field is one of the runtime's
words).

- `hmr_tp0`: at any runtime layout;
- `hmr_TP0`: at the assembled theorem's layout (`CxCore2.htp`'s thread
  pointer).
-/
import Spike.Lib.LowerX64.G1FnSpec
import Spike.Lib.Rt.X64StartArith

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Flow.Ret0 (limA pinA tpOf)
open Spike.Lib.LowerNode (imms2Me)

/-- **The first TCB's limit word is mapped** at any runtime layout `L`
(`words_mapped` at the limit field, `fld_mem`). -/
theorem hmr_tp0 (L : Spike.Lib.X64.Rt.RuntimeLayout) :
    Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false
      ⟨limA (tpOf (pinA L.lab + 0#64 + 8#64)), 8⟩ = true := by
  rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
  exact (L.words_mapped _ (L.fld_mem (by decide))).2.1

section G1Hmr

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

/-- **The first TCB's limit word is mapped** at the assembled theorem's
layout (`hmr_tp0`): `hmr` at `CxCore2.htp`'s thread pointer. -/
theorem hmr_TP0 : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false ⟨limA TP0, 8⟩ = true :=
  hmr_tp0 _

end G1Hmr

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hmr_tp0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hmr_tp0
/-- info: 'Spike.Lib.LowerX64.hmr_TP0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hmr_TP0
