/-
**hello.w: main's side after the spawn** (the twin of `WakeInst.mainInv`,
`mainWR`, `wakeM`): main's invariant over the source program `p` (wake's
`mainInv` fixes `wakeSrc`), its state predicate with the flag load's pc at
hello's `wc_waitLoop` prefix `.L21_wc_waitLoop` (wake's `mainWR` spells out
`.L20_wc_waitLoop`), and main's `MSide` at `helloSrc`, over any record type
`ι` (the instance's) with its placement, memory side and pointer word.

- `mainInvP p lbl ms W`: the union of the invariants closed under main's
  rows of `p` inside `W`; `mainInvP_closed`, `mainInvP_W`, `mainInvP_of`.
- `mainWRH lab exe Λ lbl lsize`: `WakeInst.mainWR` with the flag load's pc
  `lab (".L21_wc_waitLoop" ++ ".0_entry") + 4 + 4`.
- `helloM lbl lsize ms cw lab exe Λ μT hoff`: main's `MSide` (`p := helloSrc`,
  `Mi := mainInvP helloSrc … (mainWRH …)`, `off` from `hoff`, `wl` by
  `HelloB7b.hello_wl`).
- `hoff_ofPlaceW`: `hoff` at a placed output's runtime layout and marks
  (`A64AbOffL.off_of_A_ofPlaceOK`), so `helloM`'s `off` holds at hello's
  placed layout with no further premise.
-/
import Spike.Lib.WakeInst
import Spike.Lib.HelloB7b

namespace Spike.Lib.HelloMainInv

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.WakeInst (mainW MainSys FlagW)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **The union of the invariants closed under main's rows of `p` inside
`W`** (`WakeInst.mainInv` at `wakeSrc`). -/
def mainInvP (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isaLSE2) (W : Frag isaLSE2) :
    Frag isaLSE2 :=
  fun s c => ∃ inv : Frag isaLSE2, (∀ s c, inv s c → OutL p lbl ms inv s c) ∧
    (∀ s c, inv s c → W s c) ∧ inv s c

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {W : Frag isaLSE2}

theorem mainInvP_closed : ∀ s c, mainInvP p lbl ms W s c → OutL p lbl ms (mainInvP p lbl ms W) s c := by
  rintro s c ⟨inv, hcl, hW, hi⟩
  exact (hcl s c hi).mono fun s c h => ⟨inv, hcl, hW, h⟩

theorem mainInvP_W : ∀ s c, mainInvP p lbl ms W s c → W s c :=
  fun s c ⟨_, _, hW, hi⟩ => hW s c hi

/-- A state of an invariant closed under the rows inside `W` is in
`mainInvP`. -/
theorem mainInvP_of {inv : Frag isaLSE2} (hW : ∀ s c, inv s c → W s c)
    (hcl : ∀ s c, inv s c → OutL p lbl ms inv s c) {s : isaLSE2.State} {c : Ctl} (h : inv s c) :
    mainInvP p lbl ms W s c :=
  ⟨inv, hcl, hW, h⟩

/-- `mainInvP` at `wakeSrc` is `WakeInst.mainInv`. -/
theorem mainInvP_wake : mainInvP WakeT1.wakeSrc lbl ms W = WakeInst.mainInv lbl ms W := rfl

/-- **main's state predicate after the spawn** at hello.w's listing:
`WakeInst.mainWR` with the flag load's pc after `wc_waitLoop`'s `ldar` at
hello's prefix (`A64.HelloLabels.pfx ++ ".0_entry"`, plus the `ldar`'s 2
cells). -/
def mainWRH (lab : String → Int64) (exe : _root_.Executable) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Frag isaLSE2 :=
  fun s c => mainW lab exe Λ lbl s c ∧ Spike.Lib.A64.Flow.RelWS s ∧
    Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c ∧ MainSys s ∧
    FlagW lbl lsize (lab (".L21_wc_waitLoop" ++ ".0_entry") + 4 + 4) s c

/-- **main's side at hello.w** (see the module doc). -/
def helloM {ι : Type} (lbl : ι → WeakMem.AllocLabel → Option Nat) (lsize : ι → WeakMem.AllocLabel → Nat)
    (ms : ι → MemSide isaLSE2) (cw : ι → TermRun.Word) (lab : String → Int64) (exe : _root_.Executable)
    (Λ : Scc.Sem.Layout) (μT : Marks)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a) :
    WakeM0.MSide ι where
  p := helloSrc
  lbl := lbl
  ms := ms
  Mi w := mainInvP helloSrc (lbl w) (ms w) (mainWRH lab exe Λ (lbl w) (lsize w))
  closed _ := mainInvP_closed
  cw := cw
  μ := μT
  off _ s c h := hoff s c (mainInvP_W s c h).1.1
  wl := HelloB7b.hello_wl

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`helloM`'s `hoff` at a placed output** (hello's included): `AbOffA`
of the runtime layout's labels is off every abort site of its marks. -/
theorem hoff_ofPlaceW : ∀ s c, Spike.Lib.A64WakeOff.AbOffA (RuntimeLayout.ofPlaceW hp i).lab s c →
    ∀ k a, (Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i)).abortAt k = some a → pcOf s ≠ a :=
  fun _ _ h => Spike.Lib.A64AbOffL.off_of_A_ofPlaceOK hp i h

end Place

end Spike.Lib.HelloMainInv

/-- info: 'Spike.Lib.HelloMainInv.mainInvP_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInv.mainInvP_closed

/-- info: 'Spike.Lib.HelloMainInv.hoff_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainInv.hoff_ofPlaceW
