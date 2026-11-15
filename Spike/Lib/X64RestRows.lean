/-
**`NodesA`'s x86-64 row shapes along a map of target states** (for moving
the consumer obligations from a text to the same text with a tail
appended, `Spike/Lib/RestTail.lean`): the counter's add (`CtrRow`) and the
row after the source's publication (`PubOut`) of `s` are those of `r s`,
landing in the image of their landings, when the step of `r s` is the step
of `s` with every leaf mapped and the memory sides correspond along `r` at
`s` (`MsMap`).

- `ctrRow_map`: `CtrRow` along a state map;
- `pubOut_map`: `PubOut` along a state map, into a fragment holding the
  image of the old one.
-/
import Spike.Lib.RestTail
import Spike.Lib.X64ConsumerA

namespace Spike.Lib.X64RestRows

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (InvS OwnS)
open Spike.Lib.X64ConsumerA (CtrRow PubOut msOfAX)
open Spike.Lib.RestTail (img img_of imgS MsMap outS_map pend_map)

/-- **The counter's add along a state map**: the read-modify-write's
continuation mapped, its landing the image of the old one. -/
theorem ctrRow_map {ms ms' : MemSide isa} {X : Frag isa} {s : State} {c : Ctl} (r : State → State)
    (hex : isa.exec (r s) = (isa.exec s).map (EvTree.map r)) (hm : MsMap r ms ms' s)
    (h : CtrRow ms X s c) : CtrRow ms' (img r X) (r s) c := by
  obtain ⟨k, op, g, x, τ, e, n, he, hrt, hmp, hs, hh, hop, hX⟩ := h
  refine ⟨k, op, r ∘ g, x, τ, e, n, by rw [hex, he, hm.ctr]; rfl, by rw [hm.ctr, hm.rt]; exact hrt,
    by rw [hm.ctr, hm.mp]; exact hmp, hm.newOk ▸ hs, hh, by rw [hm.units]; exact hop, ?_⟩
  intro old hG ho hc hlo
  rw [hm.ctr, hm.G, hm.units] at *
  rw [hm.cells] at hc
  rw [hm.lo] at hlo
  have h := hX old hG (fun w hw => ho w (by rw [hm.own]; exact hw)) hc hlo
  exact ⟨h.1, img_of h.2⟩

/-- **The row after the source's publication along a state map**: the
system-call test and the memory sides commute with `r` at `s` (`hsys`,
`hm`), and the fragment `I'` holds the image of `I` (`hI`). -/
theorem pubOut_map {Λ Λ' : Scc.Sem.Layout} {p : Prog} {μ μ' : Marks} {rd rd' : TermRun.Word → Prop}
    {G G' : Loc → Val → Prop} {own own' : OwnS} {ar : Arena} {I I' : InvS} {ab ab' : Option (State → Prop)}
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} (r : State → State)
    (hex : isa.exec (r s) = (isa.exec s).map (EvTree.map r)) (hsys : abi.atSys (r s) = abi.atSys s)
    (hm : ∀ fs, MsMap r (msOfAX Λ μ p rd G own ar I ab lbl lsize fs)
      (msOfAX Λ' μ' p rd' G' own' ar I' ab' lbl lsize fs) s)
    (hI : ∀ s c fs, I lbl lsize s c fs → I' lbl lsize (r s) c fs)
    (h : PubOut Λ p μ rd G own ar I ab lbl lsize s c fs) :
    PubOut Λ' p μ' rd' G' own' ar I' ab' lbl lsize (r s) c fs := by
  obtain ⟨hns, hpub, c₁, hps, hi, ho⟩ := h
  refine ⟨hsys.trans hns, hpub, c₁, hps, hI _ _ _ hi, ?_⟩
  refine (outS_map r hex hm ho).mono fun _ _ _ ⟨s0, hp, he⟩ => ?_
  subst he
  obtain ⟨c', fs', hr, hp'⟩ := pend_map r hp
  exact ⟨c', fs', hr, by obtain ⟨s1, h1, he1⟩ := hp'; rw [he1]; exact hI _ _ _ h1⟩

end Spike.Lib.X64RestRows

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64RestRows.ctrRow_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64RestRows.ctrRow_map

/-- info: 'Spike.Lib.X64RestRows.pubOut_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64RestRows.pubOut_map
