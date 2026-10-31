/-
**Appended owned words for the held-predicate state facts** (x86-64):
`SFactsSt.appendS` and `BlkW.appendS` (`Spike/Lib/X64WakeOwnS.lean`) for
`SFactsSt2` (`Spike/Lib/X64SFactsACH.lean`), the per-state facts of a
fragment over a held predicate (wake's main), which has no range or phase
fields, plus the node version.

- `SFactsSt2.appendS`: the state facts with an appended map
  (`own s ++ ownS s`), given `AppOk`.
- `BlkW.appendS2`, `NodeW.appendS2`: a block's (a node's) states with an
  appended map, `AppOk` itself a `BlkW` (`NodeW`).
-/
import Spike.Lib.X64WakeOwnS
import Spike.Lib.X64SFactsACH

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.X64 (BlkW NodeW ND)
open Spike.Lib.X64ConsumerA (SFactsSt2)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Spike.Lib.X64Consumer.Own} {Dt : State → Prop}

/-- **The held-predicate state facts with appended words.** -/
theorem _root_.Spike.Lib.X64ConsumerA.SFactsSt2.appendS {ownS : Spike.Lib.X64Consumer.Own} {s : State}
    (h : SFactsSt2 Λ μ own s Dt)
    (ha : AppOk μ own ownS s) : SFactsSt2 Λ μ (fun s => own s ++ ownS s) s Dt where
  noSite := h.noSite
  mapped := h.mapped
  svc := h.svc
  ownInstr := fun hns tree he =>
    ownTree_append (h.ownInstr hns tree he) (fun s' hl => ha.1 s' (.inl ⟨hns, tree, he, hl⟩)) (ha.2.1 hns tree he)
      ha.2.2
  ownSys := fun hsy call hd s' hs' => by
    show own s' ++ ownS s' = own s ++ ownS s
    rw [h.ownSys hsy call hd s' hs', ha.1 s' (.inr (.inl ⟨hsy, call, hd, hs'⟩))]
  ownTake := fun a' ha' hpc m => by
    show own _ ++ ownS _ = own s ++ ownS s
    rw [h.ownTake a' ha' hpc m, ha.1 (abi.skip (abi.setDmem s m)) (.inr (.inr ⟨a', ha', hpc, m, rfl⟩))]
  site := h.site
  wrTail := h.wrTail

/-- **A block's held-predicate state facts with appended words**, `AppOk`
itself a `BlkW`. -/
theorem _root_.Spike.Lib.X64.BlkW.appendS2 {ownS : Spike.Lib.X64Consumer.Own} {K : State → State → Prop}
    {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (ha : BlkW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ μ (fun s => own s ++ ownS s) s Dt) K exe endPc R F n blk := by
  intro s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  have h1 := h s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  exact ⟨h1.1.appendS (ha s σ c he hend hd hpc hA hF hJ k hk m hAm hD).1, h1.2⟩

/-- **A node's held-predicate state facts with appended words**, `AppOk`
itself a `NodeW`. -/
theorem _root_.Spike.Lib.X64.NodeW.appendS2 {ownS : Spike.Lib.X64Consumer.Own} {K : State → State → Prop}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    (h : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (ha : NodeW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s _ => SFactsSt2 Λ μ (fun s => own s ++ ownS s) s Dt) K exe endPc R F n :=
  fun s c hat => ⟨(h s c hat).1.appendS (ha s c hat).1, (h s c hat).2⟩

/-- info: 'Spike.Lib.X64ConsumerA.SFactsSt2.appendS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SFactsSt2.appendS

/-- info: 'Spike.Lib.X64.BlkW.appendS2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.BlkW.appendS2

/-- info: 'Spike.Lib.X64.NodeW.appendS2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.NodeW.appendS2

end Spike.Lib.X64.WakePh
