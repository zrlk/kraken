/-
**State facts without a take phase under another owned-words map**
(x86-64; the twin of `Spike/Lib/Rt/A64CallSwitch2.lean`): `SFactsSt2`
(`Spike/Lib/X64SFactsACH.lean`) reads the owned words only at the state and
at its successors, so it moves to any `own'` equal to `own` there
(`SFactsSt2.congr`), a block's states the same way (`BlkW.ownCongr2`), and a
runtime `call` proved at a constant instance lands in the global map's
`SFactsSt2` (`call_switch2`, with no phase to agree on).

- `SFactsSt2.congr`: the state facts moved to an agreeing map.
- `BlkW.ownCongr2`: a block's `SFactsSt2` states moved to an agreeing map,
  the agreement itself a `BlkW` (`BlkW.agree2_of_pc`: from every state at
  the block's pcs).
- `call_switch2`: the `call fn` block inside the global map's `SFactsSt2`.

**Unlike AArch64**: as `call_switch`, no `hal` but `hcov` (the region covers
the pushed return address), the block located by `blockAtB` at a byte
offset; a block's pcs in `BlkW.agree2_of_pc` are its label's plus `cellOff`.
-/
import Spike.Lib.Rt.X64CallSwitch
import Spike.Lib.X64SFactsACH

namespace Spike.Lib.X64ConsumerA

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (BlkW ND cellOff)

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
    {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)}
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
    {n : ND} {blk : List (Directive × Nat)}
    (hag : ∀ s : State, (∃ k < blk.length, s.st.2 = n.pc + Int64.ofNat (cellOff blk k)) →
      own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s') :
    BlkW (fun s _ => own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s')
      (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨hag _ ⟨k, hk, rfl⟩, fun _ h => h⟩

end Spike.Lib.X64ConsumerA

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (SFactsSt SFactsSt2 StSucc)
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Scc.Cert.Rt.X64 (blockAtB)

/-- **A runtime call into another instance, without a take phase**: as
`call_switch`, the `call fn` block proved at the constant instance `o` (any
phase), its states inside `SFactsSt2` at the global map `own'`, given that
map equals `o` at the `call` and at each of its successors (`hag`, over the
block's facts). -/
theorem call_switch2 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own own' : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
    {lbl : Lbl} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (o : List (Loc × Val))
    {R : Region} {F : MachineData → Prop} {n : ND} {l fn : Label} {off : Nat}
    (hb : blockAtB cells l off (callB fn) = true) (he : lab l + Int64.ofNat off = n.pc)
    (hR : R.OK) (hcov : Spike.Lib.offOk R.lo R.hi (n.o.sp - 8) = true) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc n.pc.toBitVec.toNat = true) (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hag : BlkW (fun s _ => own' s = o ∧ ∀ s', StSucc μ s s' → own' s' = o) (fun _ _ => False) exe endPc R
      (fun m => F m ∧ StackM rS m) n (callB fn)) :
    BlkW (fun s _ => SFactsSt2 Λ μ own' s) K exe endPc R (fun m => F m ∧ StackM rS m) n (callB fn) := by
  have h := call_switch (Λ := Λ) (rS := rS) (lbl := lbl) (F := F) (own' := own') (Tk' := fun _ => True)
    hI o True hb he hR hcov hC hok hsub hSM
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
      let r := hag s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
      ⟨⟨⟨r.1.1, Iff.rfl⟩, fun s' hs' => ⟨r.1.2 s' hs', Iff.rfl⟩⟩, r.2⟩)
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1.toSt2, r.2⟩

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64ConsumerA.SFactsSt2.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SFactsSt2.congr

/-- info: 'Spike.Lib.X64ConsumerA.BlkW.ownCongr2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.BlkW.ownCongr2

/-- info: 'Spike.Lib.X64ConsumerA.BlkW.agree2_of_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.BlkW.agree2_of_pc

/-- info: 'Spike.Lib.X64.Rt.call_switch2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.call_switch2
