/-
**The runtime's layout from the placement check** (`Spike/Lib/Rt/A64Layout.lean`):
an AArch64 output passing `Scc.Cert.PlaceOK.A64.placeOK` at a placement
configuration (its link `tablesOf`), with its immediate table, gives its `RuntimeLayout`.

- **`RuntimeLayout.ofPlaceOK`**: the canonical loader's thread at the Linux
  entry state, its text and the link with the immediates; the layout from
  A2 (`lays_of_loadOk` after the `belowLen` cells of the data symbols
  below the code, `validLayout_of_loadOk`), the six words at their
  labels and their side conditions from A8 (`lab_link_of_placeOKAt`,
  `wordsOk_of_rtWordsOk` and `Rt.A64.words_*_of_wordsOk`).
- **Oracle checks**: at `ret0`, the record is the hand one's (`ret0L`) in
  every field but the proofs.
-/
import Spike.Lib.Rt.A64LayoutRet0
import Spike.Test.A64Ret0PlaceOK

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64 Scc.Cert.Link.A64

namespace RuntimeLayout

/-- **The runtime's layout of an output passing `placeOKAt` at a layout
`Λ`**, its link `{ Λ with imms := i }`, its executable the canonical
loader's thread's at the Linux entry state. -/
def ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) : RuntimeLayout :=
  let Λi : Scc.Sem.Layout := { Λ with imms := i }
  let A := Scc.Cert.Rt.A64.rtA Λi o.prog o.secs
  have hw := Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h)
  have hl {x : String} (hx : x ∈ Scc.Cert.Rt.A64.rtNames) := lab_link_of_placeOKAt i h hx Scc.Sem.Entry.linux
  { exe := (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux Λi.code.lo o.prog (Scc.Sem.loadSyms Λi o.secs.rodata)).exe
    prog := o.prog
    Λ := Λi
    pfx := Scc.Cert.Rt.A64.belowLen Λi.code.lo (Scc.Sem.loadSyms Λi o.secs.rodata)
    lays := lays_of_loadOk (loadOk_link_of_placeOKAt i h) _
    valid := validLayout_of_loadOk (loadOk_link_of_placeOKAt i h) _
    pinA := A "scc_rt_pinned"
    pnA := A "scc_rt_pinned_next"
    stacksA := A "scc_rt_stacks"
    nextA := A "scc_rt_stack_next"
    lockA := A "scc_rt_stack_lock"
    freeNA := A "scc_rt_stack_free_n"
    lab_pin := hl (by decide)
    lab_pn := hl (by decide)
    lab_stacks := hl (by decide)
    lab_next := hl (by decide)
    lab_lock := hl (by decide)
    lab_freeN := hl (by decide)
    words_small := Scc.Cert.Rt.A64.words_small_of_wordsOk hw
    words_pool := Scc.Cert.Rt.A64.words_pool_of_wordsOk hw
    words_mapped a ha :=
      have hm := (Scc.Cert.Rt.A64.words_mapped_of_wordsOk hw a ha).2.2
      ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem hm, Spike.Lib.A64Consumer.mapped_K0_of_mem hm, hm⟩
    pool_fit := Scc.Cert.Rt.A64.pool_fit_of_wordsOk hw
    stacks_al := Scc.Cert.Rt.A64.stacks_al_of_wordsOk hw
    stacks_sub := Scc.Cert.Rt.A64.stacks_sub_of_wordsOk hw }

/-- **No data symbol of `ofPlaceOK` below the code is named like a code
label** (A2's `noClash`): the premise of the loader's label lemma
`Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below`. -/
theorem ofPlaceOK_below {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {l : String} {a : Nat}
    (ha : codeOf (ofPlaceOK h i).Λ.code.lo o.prog l = some a) :
    ∀ p ∈ Scc.Sem.symsBelow (ofPlaceOK h i).Λ.code.lo (Scc.Sem.loadSyms (ofPlaceOK h i).Λ o.secs.rodata),
      p.1 ≠ l :=
  below_ne_of_loadOk (loadOk_link_of_placeOKAt i h) ha

/-- The words of `ofPlaceOK` are 8-aligned. -/
theorem ofPlaceOK_words_al {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) : ∀ a ∈ (ofPlaceOK h i).rtWords, a.toNat % 8 = 0 :=
  Scc.Cert.Rt.A64.words_al_of_wordsOk (Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h))

/-- **The Linux entry state is admissible at the record**: its stack is
clear of the layout (`clear_link_of_placeOKAt`), at a 16-aligned user stack
pointer with 64 KiB. -/
theorem linux_ok_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) : Scc.Sem.Entry.linux.Ok (ofPlaceOK h i).Λ :=
  ⟨clear_link_of_placeOKAt i h, by decide, by decide, by decide⟩

/-- **The witness entry state is admissible at the record**: the 64 KiB
stack at `2 ^ 32`, above every region (A1's `below32`, `Entry.ok_witness`),
so `CorrectE` at the record is not vacuous on a non-Linux stack. -/
theorem witness_ok_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}
    {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩ (ofPlaceOK h i).Λ :=
  Scc.Sem.Entry.ok_witness (below32_of_placeOKAt h)

end RuntimeLayout

/-! ## Oracle checks: `ret0`'s layout from its placement check is the hand one -/

section Oracle

open SccCode (ret0Imms)
open Ret0L (ret0L)
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK)

/-- `ret0`'s runtime layout from `ret0_placeOK`. -/
abbrev ret0P : RuntimeLayout := RuntimeLayout.ofPlaceOK (atTables ret0_placeOK) ret0Imms

example : ret0P.exe = ret0L.exe := rfl
example : ret0P.prog = ret0L.prog := rfl
example : ret0P.Λ = ret0L.Λ := rfl
example : ret0P.pinA = ret0L.pinA := by decide +kernel
example : ret0P.pnA = ret0L.pnA := by decide +kernel
example : ret0P.stacksA = ret0L.stacksA := by decide +kernel
example : ret0P.nextA = ret0L.nextA := by decide +kernel
example : ret0P.lockA = ret0L.lockA := by decide +kernel
example : ret0P.freeNA = ret0L.freeNA := by decide +kernel

end Oracle

end Spike.Lib.A64.Rt
