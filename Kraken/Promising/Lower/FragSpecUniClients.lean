/-
**Validation: both clients' `push`/`pop`
specifications from the one general specification per fragment**
(`Lower/FragSpecUni.lean`). ISA: AArch64; machine: the
executable machine's per-thread environment semantics, partial correctness.

Every theorem here is `.mono` of `pushFrag_specU`/`popFrag_specU` (or the
purity twins `pushFrag_pureU`/`popFrag_pureU`), at:
- **The first lowering pilot/the allocation pilot** (`EW P w`, frame `NoDmem`, post `CalleeSaved`): `G = ⊤`,
  `F = NoDmemD`, then `FragSpecEnv.of_vals_top` (`valsEnv E ⊤` to `E`);
- **The stack-frame pilot** (`EWV P w`, frame `StackOK`, post `Saved2`): `G = GV P`,
  `F = StackOK P lo n` (`tFrameOK_heapOff`); `pop`'s node fact (`PopRes2`) is
  `PopResU`'s `G`-value conjunct through `top_node`.

Fragment level: `Pilot.{push,pop}Frag_{spec,pure}_viaUni` coincide with
the fragment-spec layer's `Pilot.{push,pop}Frag_{spec,pure}`, and
`Pilot2.{push,pop}Frag_{spec,pure}2_viaUni` are the stack-frame pilot's specs as fragment
specs (new). Program level (one line each, `.of_placed`):
`Pilot.{push,pop}_{spec,pure}_viaUni` at `pilot` and
`Pilot2.{push,pop}_{spec,pure}2_viaUni` at `pilot2`. Each has an
`example : @X_viaUni = @X := rfl` statement check against the original theorem.
-/
import Kraken.Promising.Lower.FragSpecUni
import Kraken.Promising.Lower.FragSpecPilot
import Kraken.Promising.Lower.Pilot2Pure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

/-! ## the first lowering pilot: `G = ⊤`, `F = NoDmemD` -/

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Uni

theorem pushFrag_spec_viaUni (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FragSpecEnv (SharedEnv.counted (EW P w)) pushFrag "push" (PushPre P w) (PushPost P w) :=
  (FragSpecEnv.of_vals_top (pushFrag_specU P w hL hw _ NoDmemD (tFrameOK_noDmem P w _))).mono
    (fun _ _ _ h => h) fun _ _ _ _ _ _ ⟨hs, _, hPo⟩ => ⟨hs.1, hPo⟩

theorem popFrag_spec_viaUni (P : Params) (w : Nat) (hw : w < 2) :
    FragSpecEnv (SharedEnv.counted (EW P w)) popFrag "pop" (PopPre P w) (PopPost P w) :=
  (FragSpecEnv.of_vals_top (popFrag_specU P w hw _ NoDmemD (tFrameOK_noDmem P w _))).mono
    (fun _ _ _ h => h) fun _ _ _ _ _ _ ⟨hs, _, hR, _⟩ => ⟨hs.1, hR⟩

theorem pushFrag_pure_viaUni (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FragSpecEnv (RP rel) pushFrag "push"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushFrag_pureU rel t n hn NoDmemD fun _ hd => ⟨hd.1 _, hd.1 _⟩).mono (fun _ _ _ h => h)
    fun _ _ _ _ _ _ h => h.1.1

theorem popFrag_pure_viaUni (rel : Loc → Pred) (t : BitVec 64) :
    FragSpecEnv (RP rel) popFrag "pop"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pureU rel t NoDmemD fun _ hd => hd.1 _).mono (fun _ _ _ h => h) fun _ _ _ _ _ _ h => h.1.1

example : @pushFrag_spec_viaUni = @pushFrag_spec := rfl
example : @popFrag_spec_viaUni = @popFrag_spec := rfl
example : @pushFrag_pure_viaUni = @pushFrag_pure := rfl
example : @popFrag_pure_viaUni = @popFrag_pure := rfl

section Pilot

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot)]

attribute [local instance] pilot.env

theorem push_spec_viaUni (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "push") (PushPre P w)
      (PushPost P w) :=
  (pushFrag_spec_viaUni P w hL hw).of_placed pilot_placed (by decide)

theorem pop_spec_viaUni (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) :=
  (popFrag_spec_viaUni P w hw).of_placed pilot_placed (by decide)

theorem push_pure_viaUni (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushFrag_pure_viaUni rel t n hn).of_placed pilot_placed (by decide)

theorem pop_pure_viaUni (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pure_viaUni rel t).of_placed pilot_placed (by decide)

end Pilot

example : @push_spec_viaUni = @push_spec := rfl
example : @pop_spec_viaUni = @pop_spec := rfl
example : @push_pure_viaUni = @push_pure := rfl
example : @pop_pure_viaUni = @pop_pure := rfl

end Kraken.Promising.Lower.Pilot

/-! ## the stack-frame pilot: `G = GV P`, `F = StackOK P lo n` -/

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Uni
open Kraken.Promising.Lower.Pilot (RP pushFrag popFrag)

theorem pushFrag_spec2_viaUni (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    FragSpecEnv (SharedEnv.counted (EWV P w)) pushFrag "push" (PushPre2 P w lo n) (PushPost2 P w lo n) :=
  (pushFrag_specU P w hL hw (GV P) (StackOK P lo n) (tFrameOK_heapOff hw fun _ h => h.1)).mono
    (fun _ _ _ h => h) fun _ _ _ _ _ _ h => h

theorem popFrag_spec2_viaUni (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    FragSpecEnv (SharedEnv.counted (EWV P w)) popFrag "pop" (PopPre2 P w lo n) (PopPost2 P w lo n) :=
  (popFrag_specU P w hw (GV P) (StackOK P lo n) (tFrameOK_heapOff hw fun _ h => h.1)).mono
    (fun _ _ _ h => h) fun _ _ _ _ _ _ ⟨hs, hF, hR, hN⟩ =>
      ⟨hs, hF, hR, fun hx => by obtain ⟨v, hg, hv⟩ := hN hx; rw [← hv] at hx ⊢; exact top_node hg hx⟩

theorem pushFrag_pure2_viaUni (rel : Loc → Pred) (P : Params) (w : Nat) (hw : w < 2)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨P.n w + 8, 8⟩) v) :
    FragSpecEnv (RP rel) pushFrag "push"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') :=
  (pushFrag_pureU rel P.t (P.n w) hn (HeapOff (HP P)) fun _ hd =>
      ⟨hd.loadInt_none (hp_top P) (n := 8) (by decide), hd.loadInt_none (hp_link (pn_cases hw)) (n := 8) (by decide)⟩).mono
    (fun _ _ _ h => h) fun _ _ _ _ _ _ h => h.1

theorem popFrag_pure2_viaUni (rel : Loc → Pred) (P : Params) :
    FragSpecEnv (RP rel) popFrag "pop" (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') :=
  (popFrag_pureU rel P.t (HeapOff (HP P)) fun _ hd => hd.loadInt_none (hp_top P) (n := 8) (by decide)).mono
    (fun _ _ _ h => h) fun _ _ _ _ _ _ h => h.1

section Pilot2

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

attribute [local instance] pilot2.env

theorem push_spec2_viaUni (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "push")
      (PushPre2 P w lo n) (PushPost2 P w lo n) :=
  (pushFrag_spec2_viaUni P w hL hw lo n).of_placed pilot2_placed (by decide)

theorem pop_spec2_viaUni (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "pop")
      (PopPre2 P w lo n) (PopPost2 P w lo n) :=
  (popFrag_spec2_viaUni P w hw lo n).of_placed pilot2_placed (by decide)

theorem push_pure2_viaUni (rel : Loc → Pred) (P : Params) (w : Nat) (hw : w < 2)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨P.n w + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') :=
  (pushFrag_pure2_viaUni rel P w hw hn).of_placed pilot2_placed (by decide)

theorem pop_pure2_viaUni (rel : Loc → Pred) (P : Params) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') :=
  (popFrag_pure2_viaUni rel P).of_placed pilot2_placed (by decide)

end Pilot2

example : @push_spec2_viaUni = @push_spec2 := rfl
example : @pop_spec2_viaUni = @pop_spec2 := rfl
example : @push_pure2_viaUni = @push_pure2 := rfl
example : @pop_pure2_viaUni = @pop_pure2 := rfl

end Kraken.Promising.Lower.Pilot2
