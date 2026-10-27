/-
**The runtime's layout from the placement check on x86-64**
(`Spike/Lib/Rt/X64Layout.lean`): an x86-64 output passing
`Scc.Cert.PlaceOK.X64.placeOK` at a placement configuration, with its
immediate table, gives its `RuntimeLayout`. The x86-64 twin of
`Spike/Lib/Rt/A64LayoutOfPlaceOK.lean`.

- **`RuntimeLayout.ofPlaceOK`**: the canonical loader's thread at the Linux
  entry state, its code cells and the link with the immediates; the layout
  from A2 (`lays_of_loadOk` after the `belowLen` cells of the data symbols
  below the code, `validLayout_of_loadOk`), the six words at their
  labels and their side conditions from A8 (`lab_link_of_placeOKAt`,
  `wordsOk_of_rtWordsOk` and `Rt.X64.words_*_of_wordsOk`).
- **Oracle checks**: at `ret0`, the record is the hand one's (`ret0L`) in
  every field but the proofs.
-/
import Spike.Lib.Rt.X64LayoutRet0
import Spike.Test.X64Ret0PlaceOK

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64 Scc.Cert.Link.X64

namespace RuntimeLayout

/-- **The runtime's layout of an output passing `placeOKAt` at a layout
`Λ`** (the static link, or one read off an executable), its link
`{ Λ with imms := i }`, its executable the canonical loader's thread's at
the Linux entry state. -/
def ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) : RuntimeLayout :=
  let Λ : Scc.Sem.Layout := { Λ with imms := i }
  let A := Scc.Cert.Rt.X64.rtA Λ o.prog o.secs
  have hw := Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h)
  have hl {x : String} (hx : x ∈ Scc.Cert.Rt.X64.rtNames) := lab_link_of_placeOKAt i h hx Scc.Sem.Entry.linux
  { exe := (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe
    prog := o.prog
    Λ := Λ
    pfx := belowLen Λ.code.lo (Scc.Sem.loadSyms Λ o.secs.rodata)
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
    words_small := Scc.Cert.Rt.X64.words_small_of_wordsOk hw
    words_pool := Scc.Cert.Rt.X64.words_pool_of_wordsOk hw
    words_mapped a ha :=
      have hm := (Scc.Cert.Rt.X64.words_mapped_of_wordsOk hw a ha).2.2
      ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem hm, Spike.Lib.X64Consumer.mapped_K0_of_mem hm, hm⟩
    pool_fit := Scc.Cert.Rt.X64.pool_fit_of_wordsOk hw
    stacks_al := Scc.Cert.Rt.X64.stacks_al_of_wordsOk hw
    stacks_sub := Scc.Cert.Rt.X64.stacks_sub_of_wordsOk hw }

/-- **No data symbol of `ofPlaceOK` below the code is named like a code
label** (A2's `noClash`): the premise of the loader's label lemma
`Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below`. -/
theorem ofPlaceOK_below {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {l : String} {a : Nat}
    (ha : Scc.Sem.X64.codeLabel (ofPlaceOK h i).Λ.code.lo o.prog l = some a) :
    ∀ p ∈ Scc.Sem.symsBelow (ofPlaceOK h i).Λ.code.lo (Scc.Sem.loadSyms (ofPlaceOK h i).Λ o.secs.rodata),
      p.1 ≠ l :=
  below_ne_of_loadOk (loadOk_link_of_placeOKAt i h) ha

/-- The words of `ofPlaceOK` are 8-aligned. -/
theorem ofPlaceOK_words_al {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) : ∀ a ∈ (ofPlaceOK h i).rtWords, a.toNat % 8 = 0 :=
  Scc.Cert.Rt.X64.words_al_of_wordsOk (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h))

/-- **The words of `ofPlaceOK` are off the allocator's counter** (A8's
`ctrSepOk`): none is the word at `scc_rt_heap_use` (`heapUseOf`, the
arena's `ctrLoc`). -/
theorem hctr_of_placeOKAt {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ∀ a ∈ (ofPlaceOK h i).rtWords,
      (⟨a, 8⟩ : Loc) ≠ ⟨BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (ofPlaceOK h i).Λ), 8⟩ := by
  intro a ha he
  have hs : Scc.Cert.Rt.X64.WordSep a (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (ofPlaceOK h i).Λ)) :=
    Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h) a ha
  have ha' : a = BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (ofPlaceOK h i).Λ) := congrArg Loc.addr he
  unfold Scc.Cert.Rt.X64.WordSep at hs
  rw [← ha'] at hs
  omega

/-- **The Linux entry state is admissible at the record**: its stack is
clear of the layout (`clear_link_of_placeOKAt`), at a 16-aligned user stack
pointer with 64 KiB. -/
theorem linux_ok_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) : Scc.Sem.Entry.linux.Ok (ofPlaceOK h i).Λ :=
  ⟨clear_link_of_placeOKAt i h, by decide, by decide, by decide⟩

/-- **The witness entry state is admissible at the record**: the 64 KiB
stack at `2 ^ 32`, above every region (A1's `below32`, `Entry.ok_witness`),
so `CorrectE` at the record is not vacuous on a non-Linux stack. -/
theorem witness_ok_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩ (ofPlaceOK h i).Λ :=
  Scc.Sem.Entry.ok_witness (below32_of_placeOKAt h)

/-- info: 'Spike.Lib.X64.Rt.RuntimeLayout.hctr_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hctr_of_placeOKAt

end RuntimeLayout

/-! ## Oracle checks: `ret0`'s layout from its placement check is the hand one -/

section Oracle

open SccCode (ret0Imms)
open Ret0L (ret0L)
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)

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

end Spike.Lib.X64.Rt
