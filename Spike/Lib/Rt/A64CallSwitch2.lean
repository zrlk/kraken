/-
**State facts without a take phase under another owned-words map**
(AArch64): `SFactsSt2` (`Spike/Lib/A64SFactsACH.lean`) reads the owned words
only at the state and at its successors, so it moves to any `own'` equal to
`own` there (`SFactsSt2.congr`), a block's states the same way
(`BlkW.ownCongr2`), and a runtime `bl` proved at a constant instance lands
in the global map's `SFactsSt2` (`call_switch2`, with no phase to agree on).

- `SFactsSt2.congr`: the state facts moved to an agreeing map.
- `BlkW.ownCongr2`: a block's `SFactsSt2` states moved to an agreeing map,
  the agreement itself a `BlkW` (`BlkW.agree2_of_pc`: from every state at
  the block's pcs).
- `call_switch2`: the `bl fn` block inside the global map's `SFactsSt2`.
-/
import Spike.Lib.Rt.A64CallSwitch
import Spike.Lib.A64SFactsACH

namespace Spike.Lib.A64ConsumerA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (BlkW ND)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own own' : Own} {s : State} {Dt : State → Prop}

/-- **The state facts at an agreeing map**: `own'` equal to `own` at `s`
and at every successor of `s`. -/
theorem SFactsSt2.congr (h : SFactsSt2 Λ μ own s Dt) (hs : own' s = own s)
    (hsucc : ∀ s', StSucc μ s s' → own' s' = own s') : SFactsSt2 Λ μ own' s Dt where
  noSite := h.noSite
  mapped := h.mapped
  svc := h.svc
  ownInstr := fun hns tree he => by
    rw [hs]
    exact ownTree_congr (fun s' hl => hsucc s' (.inl ⟨hns, tree, he, hl⟩)) (h.ownInstr hns tree he)
  ownSys := fun hsy call hd s' hs' => by
    rw [hs, hsucc s' (.inr (.inl ⟨hsy, call, hd, hs'⟩))]
    exact h.ownSys hsy call hd s' hs'
  ownTake := fun a ha hpc m => by
    rw [hs, hsucc _ (.inr (.inr ⟨a, ha, hpc, m, rfl⟩))]
    exact h.ownTake a ha hpc m
  site := h.site
  wrTail := h.wrTail

/-- **A block's states at an agreeing map**: the maps agree at every state
of the block and each of its successors, as far as the block's own facts
say (`hag`, a `BlkW` of the agreement). -/
theorem BlkW.ownCongr2 {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive}
    (h : BlkW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n blk)
    (hag : BlkW (fun s _ => own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s')
      (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ μ own' s Dt) K exe endPc R F n blk := by
  intro s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  have h1 := h s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  have h2 := (hag s σ c he hend hd hpc hA hF hJ k hk m hAm hD).1
  exact ⟨h1.1.congr h2.1 h2.2, h1.2⟩

/-- **A block's agreement from every state at its pcs** (no use of the
block's facts). -/
theorem BlkW.agree2_of_pc {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List Directive}
    (hag : ∀ s : State, (∃ k < blk.length, s.st.2 = n.pc + Int64.ofNat (4 * k)) →
      own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s') :
    BlkW (fun s _ => own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s')
      (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨hag _ ⟨k, hk, rfl⟩, fun _ h => h⟩

/-- info: 'Spike.Lib.A64ConsumerA.BlkW.ownCongr2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerA.BlkW.ownCongr2

end Spike.Lib.A64ConsumerA

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (SFactsSt SFactsSt2 StSucc)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackM)
open Scc.Cert.Rt.A64 (blockAt)

/-- **A runtime call into another instance, without a take phase**: as
`call_switch`, the `bl fn` block proved at the constant instance `o` (any
phase), its states inside `SFactsSt2` at the global map `own'`, given that
map equals `o` at the `bl` and at each of its successors (`hag`, over the
block's facts). -/
theorem call_switch2 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own own' : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
    {lbl : Lbl} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (o : List (Loc × Val))
    {R : Region} {F : MachineData → Prop} {n : ND} {l fn : Label} {k : Nat}
    (hb : blockAt prog l k [blD fn] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc n.pc.toBitVec.toNat = true) (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hag : BlkW (fun s _ => own' s = o ∧ ∀ s', StSucc μ s s' → own' s' = o) (fun _ _ => False) exe endPc R
      (fun m => F m ∧ StackM rS m) n [blD fn]) :
    BlkW (fun s _ => SFactsSt2 Λ μ own' s) K exe endPc R (fun m => F m ∧ StackM rS m) n [blD fn] := by
  have h := call_switch (Λ := Λ) (rS := rS) (lbl := lbl) (F := F) (own' := own') (Tk' := fun _ => True)
    hI o True hb he hR hal hC hok hsub hSM
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
      let r := hag s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
      ⟨⟨⟨r.1.1, Iff.rfl⟩, fun s' hs' => ⟨r.1.2 s' hs', Iff.rfl⟩⟩, r.2⟩)
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1.toSt2, r.2⟩

/-- info: 'Spike.Lib.A64.Rt.call_switch2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.call_switch2

end Spike.Lib.A64.Rt
