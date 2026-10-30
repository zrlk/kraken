/-
**The state facts under another owned-words map and phase** (AArch64):
`SFactsSt` (`Spike/Lib/A64SFactsA.lean`) reads the owned words `own` and the
take's phase `Tk` only at the state and at its successors (the leaves of
its instruction, the resumptions of its system call, the states after the
take), so it moves to any `own'`, `Tk'` agreeing with them there. A block's
states are moved the same way (`BlkW.ownCongr`). This is how one instance's
facts (`InstOk` at its `own`, `Tk`, phase map) are lifted to a global map
that picks the instance from the thread state.

- `StSucc μ s s'`: `s'` is a successor of `s`.
- `Agree own Tk own' Tk' s`: the maps agree at `s`.
- `allInv_congr`, `ownTree_congr`: `AllInv` and `OwnTree` moved along the
  leaves.
- `SFactsSt.congr`: the state facts moved to agreeing maps.
- `BlkW.ownCongr`: a block's `SFactsSt` states moved to agreeing maps, the
  agreement itself a `BlkW` (`BlkW.agree_of_pc`: from every state at the
  block's pcs).
-/
import Spike.Lib.A64SFactsA

namespace Spike.Lib.A64ConsumerA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (BlkW ND)

/-- **`s'` is a successor of `s`**: a leaf of its instruction (off a system
call), a resumption of its system call, or a state after the take at the
take site. -/
def StSucc (μ : Marks) (s s' : State) : Prop :=
  (abi.atSys s = false ∧ ∃ tree, isaLSE2.exec s = some tree ∧ TreeLeaf tree s') ∨
    (abi.atSys s = true ∧ ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      s' ∈ Kernel.certSuccs abi s call) ∨
    (∃ a, μ.site .take = some a ∧ pcOf s = a ∧ ∃ m, s' = abi.skip (abi.setDmem s m))

/-- **The maps agree at `s`.** -/
def Agree (own : Own) (Tk : State → Prop) (own' : Own) (Tk' : State → Prop) (s : State) : Prop :=
  own' s = own s ∧ (Tk' s ↔ Tk s)

/-- **`AllInv` moved along the leaves.** -/
theorem allInv_congr {σ : Type} {G : Loc → Val → Prop} {Q Q' : σ → Prop} :
    ∀ {t : EvTree σ}, (∀ s, TreeLeaf t s → Q s → Q' s) → t.AllInv G Q → t.AllInv G Q'
  | .done _, hQ, h => hQ _ rfl h
  | .fault _, _, h => h
  | .choose _ _, hQ, h => fun i => allInv_congr (fun s hs => hQ s ⟨i, hs⟩) (h i)
  | .load _ _ _ _, hQ, h => fun v hv => allInv_congr (fun s hs => hQ s ⟨v, hs⟩) (h v hv)
  | .store _ _ _ _ _, hQ, h => ⟨h.1, fun b hb => allInv_congr (fun s hs => hQ s ⟨b, hs⟩) (h.2 b hb)⟩
  | .rmw _ _ _ _ _, hQ, h => fun v hv => ⟨(h v hv).1, allInv_congr (fun s hs => hQ s ⟨v, hs⟩) (h v hv).2⟩
  | .fence _ _, hQ, h => fun u => allInv_congr (fun s hs => hQ s ⟨u, hs⟩) (h u)

/-- **`OwnTree` moved along the leaves**: another map equal at every leaf. -/
theorem ownTree_congr {σ : Type} {own own' : σ → List (Loc × Val)} {ow : List (Loc × Val)} {t : EvTree σ}
    (he : ∀ s, TreeLeaf t s → own' s = own s) (h : OwnTree own ow t) : OwnTree own' ow t := by
  rcases h with ⟨hA, hW⟩ | ⟨h0, kr, L, V, s', rfl, hb, hs⟩ | ⟨kr, L, V, s', rfl, hb, hs⟩ |
    ⟨k, nr, L, op, g, rfl, hb, hin, hu⟩
  · exact .inl ⟨allInv_congr (fun s hs h => (he s hs).trans h) hA, hW⟩
  · exact .inr (.inl ⟨h0, kr, L, V, s', rfl, hb, (he s' ⟨true, rfl⟩).trans hs⟩)
  · exact .inr (.inr (.inl ⟨kr, L, V, s', rfl, hb, (he s' ⟨true, rfl⟩) ▸ hs⟩))
  · exact .inr (.inr (.inr ⟨k, nr, L, op, g, rfl, hb, hin, fun v hv => (he (g v) ⟨v, rfl⟩) ▸ hu v hv⟩))

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own own' : Own} {rS : Range} {Tk Tk' : State → Prop}
  {s : State} {Dt : State → Prop}

/-- **The state facts at agreeing maps**: `own'`, `Tk'` equal to `own`, `Tk`
at `s` and at every successor of `s`. -/
theorem SFactsSt.congr (h : SFactsSt Λ μ own rS Tk s Dt) (hs : Agree own Tk own' Tk' s)
    (hsucc : ∀ s', StSucc μ s s' → Agree own Tk own' Tk' s') : SFactsSt Λ μ own' rS Tk' s Dt where
  noSite := h.noSite
  mapped := h.mapped
  svc := h.svc
  ownInstr := fun hns tree he => by
    rw [hs.1]
    exact ownTree_congr (fun s' hl => (hsucc s' (.inl ⟨hns, tree, he, hl⟩)).1) (h.ownInstr hns tree he)
  ownSys := fun hsy call hd s' hs' => by
    rw [hs.1, (hsucc s' (.inr (.inl ⟨hsy, call, hd, hs'⟩))).1]
    exact h.ownSys hsy call hd s' hs'
  ownTake := fun a ha hpc m => by
    rw [hs.1, (hsucc _ (.inr (.inr ⟨a, ha, hpc, m, rfl⟩))).1]
    exact h.ownTake a ha hpc m
  site := fun a ha hpc => by
    rw [hs.2]
    exact h.site a ha hpc
  tkTake := fun a ha hpc m => (hsucc _ (.inr (.inr ⟨a, ha, hpc, m, rfl⟩))).2.mpr (h.tkTake a ha hpc m)
  tkInstr := fun hn hns tree he =>
    allInv_congr (fun s' hl h' => by
      rw [(hsucc s' (.inl ⟨hns, tree, he, hl⟩)).2, hs.2]; exact h') (h.tkInstr hn hns tree he)
  tkSys := fun hsy call hd s' hs' => by
    rw [(hsucc s' (.inr (.inl ⟨hsy, call, hd, hs'⟩))).2, hs.2]
    exact h.tkSys hsy call hd s' hs'
  owned := fun ht => h.owned (hs.2.mp ht)
  wrTail := h.wrTail

/-- **A block's states at agreeing maps**: the maps agree at every state of
the block and each of its successors, as far as the block's own facts say
(`hag`: a `BlkW` of the agreement, so it may use the region, the frame
condition and the invariant, e.g. which ranges the private memory maps). -/
theorem BlkW.ownCongr {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive}
    (h : BlkW (fun s _ => SFactsSt Λ μ own rS Tk s Dt) K exe endPc R F n blk)
    (hag : BlkW (fun s _ => Agree own Tk own' Tk' s ∧ ∀ s', StSucc μ s s' → Agree own Tk own' Tk' s')
      (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s _ => SFactsSt Λ μ own' rS Tk' s Dt) K exe endPc R F n blk := by
  intro s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  have h1 := h s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  have h2 := (hag s σ c he hend hd hpc hA hF hJ k hk m hAm hD).1
  exact ⟨h1.1.congr h2.1 h2.2, h1.2⟩

/-- **A block's agreement from every state at its pcs** (no use of the
block's facts). -/
theorem BlkW.agree_of_pc {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {blk : List Directive}
    (hag : ∀ s : State, (∃ k < blk.length, s.st.2 = n.pc + Int64.ofNat (4 * k)) →
      Agree own Tk own' Tk' s ∧ ∀ s', StSucc μ s s' → Agree own Tk own' Tk' s') :
    BlkW (fun s _ => Agree own Tk own' Tk' s ∧ ∀ s', StSucc μ s s' → Agree own Tk own' Tk' s')
      (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨hag _ ⟨k, hk, rfl⟩, fun _ h => h⟩

/-- info: 'Spike.Lib.A64ConsumerA.BlkW.ownCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerA.BlkW.ownCongr

end Spike.Lib.A64ConsumerA
