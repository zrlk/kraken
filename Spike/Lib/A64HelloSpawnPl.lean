/-
**Main's source at the spawn placed at `wc_main`'s slots** (AArch64; the
hello twin of `WakeSrcCtl.placedSE_spawnAt` and `WakePlacedCal.hti_placed`,
for `H1GAH.hpl`). Hello's packet `p` is the slice's three words, the box's
cell and main's id (`SpawnSrcH`), so placing `c0` takes the slice's slots
besides the cell's (`-104`) and main's id's (`-112`): `wc_main` spills the
slice's `x0`, `x2`, `x3` at `-144`, `-128`, `-120` (`WcSp6.FrWH`), and at
its entry they are rodata's slice (`HelloH2G.hG_of`).

- (`Ti2.SlotRdH`, `Ti2.SlotSlH`, `Ti2.slotSlH_keep`: the slice's slots, in
  `A64HelloTi2SlotSl`, which `Ti2Hat` imports.)
- `placedSE_spawnAtH`: at `SpawnSrcH l [w0, w1, w2]`, `c` at a place and `p`
  at five (the generic placement `WakeSrcCtl.placedSE_of_tbl`).
- `placedSE_slotsH`: at `SlotPH ∧ SlotSlH`, the slice `SlRep` at the slots.
- `placedSE_boxAtH`, `placedSE_boxSlotsH`, `hplQ_GJ1H`: the same at the box's fence (`QBH`, free variables
  `o`, `sl`, `me`; `wcWf` at the fence node).
- `hpl_GJ1H`: `H1GAH.hpl`'s statement at `SlotPH ∧ SlotSlH` (not `SlotPH`
  alone: the slice's words have no other place), at a ghost of `GJ1H` with
  the box's label `l'` fresh at `lbl1`.

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloTi2SlotSl
import Spike.Lib.A64HelloH2G
import Spike.Lib.A64HelloH1A
import Spike.Lib.A64WakeSrcCtl

namespace Spike.Lib.A64.HelloPh.SpawnPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region Ctl)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.HelloHMid (slWsH SBH QBH)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.HelloWc (FrMGH)
open Spike.Lib.A64.HelloPh.Ti2 (SlotPH SlotSlH slotRdH_place)

variable {L : RuntimeLayout} {R : Region}

/-- **main's source at the spawn placed at any six places** (wake's
`WakeSrcCtl.placedSE_spawnAt`): `c` at `pc`; `p` at `pb`, `p2`, `p3` (the
slice's words `w0`, `w1`, `w2`), `pc` and `pm`, given each place represents
its word (`lbl` puts `l` at `pc`'s word and main's id at `pm`'s). -/
theorem placedSE_spawnAtH {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    {w0 w1 w2 : TermRun.Word} (pb p2 p3 pc pm : Place (machine (kernel 1)).I.RegId)
    (hsrc : SpawnSrcH l [w0, w1, w2] c)
    (h0 : ∃ v, placeVal (machine (kernel 1)) s pb = some v ∧ ValRep lbl w0.val v)
    (h1 : ∃ v, placeVal (machine (kernel 1)) s p2 = some v ∧ ValRep lbl w1.val v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s p3 = some v ∧ ValRep lbl w2.val v)
    (hc : ∃ v, placeVal (machine (kernel 1)) s pc = some v ∧ lbl l = some v)
    (hm : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  obtain ⟨ht, -, hcc, -, -, hpp⟩ := hsrc
  simp only [TermRun.evalAt] at hcc hpp
  refine Spike.Lib.WakeSrcCtl.placedSE_of_tbl
    [("c", [.one pc]), ("p", [.one pb, .one p2, .one p3, .one pc, .one pm])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [ht, show exprFv Spike.Lib.HelloMainPreSrc.spawnTermH = ["p", "c"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hpp] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hcc] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases ex : x = "c"
    · subst ex; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hcc] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.WakeSrcCtl.rep_at hc
    by_cases ep : x = "p"
    · subst ep; simp [List.lookup] at hpl; subst hpl
      rw [hpp] at hl; cases hl
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact h0
      | 1, hwp, hwd => cases hwp; cases hwd; exact h1
      | 2, hwp, hwd => cases hwp; cases hwd; exact h2
      | 3, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.WakeSrcCtl.rep_at hc
      | 4, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.WakeSrcCtl.rep_at hm
    · simp [List.lookup, beq_false_of_ne ex, beq_false_of_ne ep] at hpl
  · intro x pls k n hpl hn'
    by_cases ex : x = "c"
    · subst ex; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases ep : x = "p"
    · subst ep; simp [List.lookup] at hpl; subst hpl
      match k, hn' with
      | 0, hn' => cases hn'
      | 1, hn' => cases hn'
      | 2, hn' => cases hn'
      | 3, hn' => cases hn'
      | 4, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne ex, beq_false_of_ne ep] at hpl

/-- **main's source at the spawn placed at `wc_main`'s slots**: the slice
(`SlRep` at `w0`, `w2`, `w3`) at `-144`, `-128`, `-120`, the box's cell `b`
at `-104` and main's id `t0` at `-112`. -/
theorem placedSE_slotsH {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    {ws : List TermRun.Word} {w0 w1 w2 w3 b t0 : Nat} (hsrc : SpawnSrcH l ws c) (hsl : SlRep lbl ws w0 w1 w2 w3)
    (hb : lbl l = some b) (ht : lbl (mainTidLbl 2) = some t0) (hP : SlotPH R b t0 s.st.1)
    (hS : SlotSlH R w0 w2 w3 s.st.1) : PlacedSE Λ lbl s c [] := by
  obtain ⟨lr, rfl, hl, -, rfl, rfl⟩ := hsl
  obtain ⟨p104, p112⟩ := Ti2.slotPH_place hP
  obtain ⟨s0, s2, s3⟩ := hS
  exact placedSE_spawnAtH _ _ _ _ _ hsrc
    ⟨_, slotRdH_place s0, by decide, w0, by simp [Scc.Sem.wordAddr, hl], by simp⟩
    ⟨_, slotRdH_place s2, by decide, rfl⟩ ⟨_, slotRdH_place s3, by decide, rfl⟩ ⟨_, p104, hb⟩ ⟨_, p112, ht⟩

/-- **`H1GAH.hpl` at `SlotPH ∧ SlotSlH`**, at a ghost of `GJ1H` (rodata's
label `lr`, the box's `l'` fresh at `lbl1`, main's id at the TCB): `c0` at
the clone's source `SBH l' b' (slWsH lr)`, the slice `sl` and main's word
`me` of an entry state of `J1`, is placed at the twice extended placement
wherever the slots read `b'`, `me` and `sl` (wake's
`WakePlacedCal.hti_placed`). -/
theorem hpl_GJ1H {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat} {F : MachineData → Prop}
    {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {t : UInt64}
    (hl' : lbl1 l' = none) (hmt : lbl1 (mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.HelloH2G.GJ1H L lbl1 lr R F J1 t) :
    ∀ c0 sl me cA fr, MidG (SBH l' b' (slWsH lr)) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b' me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE L.Λ (Spike.Lib.A64ConsumerA.upd lbl1 l' b') s c0 [] := by
  rintro c0 sl me cA fr ⟨⟨_, _, ⟨-, -, hsrc⟩, -⟩, σe, c, hJ, -, rfl, rfl⟩ s ⟨hP, hS⟩
  obtain ⟨hsl, hme⟩ := Spike.Lib.HelloH2G.hG_of (b' := b') hl' hmt R F J1 t hG σe c hJ
  exact placedSE_slotsH hsrc hsl (by simp [Spike.Lib.A64ConsumerA.upd]) hme hP hS

/-! ## At the fence (`QBH`) -/

/-- **main's source at the box's fence placed at any five places**: `o` at
`po`, `me` at `pm`, `sl` at `pb`, `p2`, `p3` (the slice's words `w0`, `w1`,
`w2`), given each place represents its word (`lbl` puts `l` at `po`'s word
and main's id at `pm`'s). -/
theorem placedSE_boxAtH {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l l' : WeakMem.AllocLabel}
    {b A : Nat} {w0 w1 w2 : TermRun.Word} (pb p2 p3 po pm : Place (machine (kernel 1)).I.RegId)
    (hsrc : QBH l b [w0, w1, w2] l' A c)
    (h0 : ∃ v, placeVal (machine (kernel 1)) s pb = some v ∧ ValRep lbl w0.val v)
    (h1 : ∃ v, placeVal (machine (kernel 1)) s p2 = some v ∧ ValRep lbl w1.val v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s p3 = some v ∧ ValRep lbl w2.val v)
    (ho : ∃ v, placeVal (machine (kernel 1)) s po = some v ∧ lbl l = some v)
    (hm : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  obtain ⟨-, -, ht, -, hoo, hme, hsl⟩ := hsrc
  simp only [TermRun.evalAt] at hoo hme hsl
  refine Spike.Lib.WakeSrcCtl.placedSE_of_tbl
    [("o", [.one po]), ("me", [.one pm]), ("sl", [.one pb, .one p2, .one p3])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [ht, show exprFv Spike.Lib.HelloMainPreSrc.boxTermH = ["o", "sl", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hoo] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hsl] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hme] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases eo : x = "o"
    · subst eo; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hoo] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.WakeSrcCtl.rep_at ho
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hme] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.WakeSrcCtl.rep_at hm
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      rw [hsl] at hl; cases hl
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact h0
      | 1, hwp, hwd => cases hwp; cases hwd; exact h1
      | 2, hwp, hwd => cases hwp; cases hwd; exact h2
    · simp [List.lookup, beq_false_of_ne eo, beq_false_of_ne em, beq_false_of_ne es] at hpl
  · intro x pls k n hpl hn'
    by_cases eo : x = "o"
    · subst eo; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      match k, hn' with
      | 0, hn' => cases hn'
      | 1, hn' => cases hn'
      | 2, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne eo, beq_false_of_ne em, beq_false_of_ne es] at hpl

/-- **main's source at the box's fence placed at `wc_main`'s slots**: the
slice (`SlRep` at `w0`, `w2`, `w3`) at `-144`, `-128`, `-120`, the box's
cell `b` at `-104` and main's id `t0` at `-112`. -/
theorem placedSE_boxSlotsH {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l l' : WeakMem.AllocLabel}
    {A : Nat} {ws : List TermRun.Word} {w0 w1 w2 w3 b t0 : Nat} (hsrc : QBH l b ws l' A c)
    (hsl : SlRep lbl ws w0 w1 w2 w3) (hb : lbl l = some b) (ht : lbl (mainTidLbl 2) = some t0)
    (hP : SlotPH R b t0 s.st.1) (hS : SlotSlH R w0 w2 w3 s.st.1) : PlacedSE Λ lbl s c [] := by
  obtain ⟨lr, rfl, hl, -, rfl, rfl⟩ := hsl
  obtain ⟨p104, p112⟩ := Ti2.slotPH_place hP
  obtain ⟨s0, s2, s3⟩ := hS
  exact placedSE_boxAtH _ _ _ _ _ hsrc
    ⟨_, slotRdH_place s0, by decide, w0, by simp [Scc.Sem.wordAddr, hl], by simp⟩
    ⟨_, slotRdH_place s2, by decide, rfl⟩ ⟨_, slotRdH_place s3, by decide, rfl⟩ ⟨_, p104, hb⟩ ⟨_, p112, ht⟩

/-- **`hpl`'s twin at the box's fence** (`hplQ`, `wcWf` at the fence
node `f`): `hpl_GJ1H` with the box's source facts `QBH l' b' (slWsH lr)`
for the clone's source. -/
theorem hplQ_GJ1H {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat} {F : MachineData → Prop}
    {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {t : UInt64}
    (hl' : lbl1 l' = none) (hmt : lbl1 (mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.HelloH2G.GJ1H L lbl1 lr R F J1 t) :
    ∀ c0 sl me cA fr, MidG (QBH l' b' (slWsH lr)) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b' me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE L.Λ (Spike.Lib.A64ConsumerA.upd lbl1 l' b') s c0 [] := by
  rintro c0 sl me cA fr ⟨⟨_, _, hsrc, -⟩, σe, c, hJ, -, rfl, rfl⟩ s ⟨hP, hS⟩
  obtain ⟨hsl, hme⟩ := Spike.Lib.HelloH2G.hG_of (b' := b') hl' hmt R F J1 t hG σe c hJ
  exact placedSE_boxSlotsH hsrc hsl (by simp [Spike.Lib.A64ConsumerA.upd]) hme hP hS

end Spike.Lib.A64.HelloPh.SpawnPl

/-- info: 'Spike.Lib.A64.HelloPh.SpawnPl.placedSE_spawnAtH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SpawnPl.placedSE_spawnAtH

/-- info: 'Spike.Lib.A64.HelloPh.SpawnPl.placedSE_slotsH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SpawnPl.placedSE_slotsH

/-- info: 'Spike.Lib.A64.HelloPh.SpawnPl.hpl_GJ1H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SpawnPl.hpl_GJ1H

/-- info: 'Spike.Lib.A64.HelloPh.SpawnPl.placedSE_boxAtH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SpawnPl.placedSE_boxAtH

/-- info: 'Spike.Lib.A64.HelloPh.SpawnPl.placedSE_boxSlotsH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SpawnPl.placedSE_boxSlotsH

/-- info: 'Spike.Lib.A64.HelloPh.SpawnPl.hplQ_GJ1H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SpawnPl.hplQ_GJ1H
